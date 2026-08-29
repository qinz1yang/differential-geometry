import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalPathDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSDecompositionPathIntegral
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSDecompositionField
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RicciConnectionDifferencePairing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrectionZeroSplit
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricCoefficientBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H1H2OperatorFieldApplication
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H1H2OperatorFieldComposition
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2H4Principal
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ParametricJetIntegral
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrectionZeroTraceRadiusFreeBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrectionZeroVectorBundleExpansion
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrectionZeroCoefficientDifferenceRadiusFree
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciConnectionDifferenceOrderOneBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.DeTurckLieFirstOrderBounds

noncomputable section
open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff
namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open LieCorrectionZeroCore
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M]
  [sigmaCompactSpace : SigmaCompactSpace M]
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] in
omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
private theorem zero_eq_unit (x : M) (D : Tensor0SSpace 0 I x) :
    D = (Tensor0SNabla.tensor0Iso I M x D) •
      unitTensor (I := I) (M := M) x := by
  classical
  have hunit :
      Tensor0SNabla.tensor0Iso I M x
          (unitTensor (I := I) (M := M) x) = (1 : ℝ) := by
    have h := Tensor0SNabla.scalarFn_unitZero (I := I) (M := M)
    have hx := congrFun h x
    simpa [Tensor0SNabla.scalarFn_apply, unitTensor] using hx
  apply (Tensor0SNabla.tensor0Iso I M x).injective
  rw [map_smul, hunit, smul_eq_mul, mul_one]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem permCoeff_app
    (g : SmoothRiemannianMetric I M) {d : ℕ}
    (ρ : Equiv.Perm (Fin d)) (S : SmoothCcTensor g 0 d) :
    ccOperatorFieldComp (I := I) (M := M) g 0 d d
        (permCoeff (I := I) (M := M) g ρ) S =
      domDomCongrSection (I := I) g ρ S := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  rw [domDomCongrSection_unitModel]
  rw [unitModel, operatorFieldComposition_toSection, ContinuousLinearMap.comp_apply]
  change Tensor0SSpace.toModel
      (slotPermCLM (I := I) ρ x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace d I x from
          S.toSection x) (unitTensor (I := I) (M := M) x))) = _
  rw [slotPermCLM_apply, Tensor0SSpace.toModel_ofModel]
  rfl
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem app_smul_left
    (g : SmoothRiemannianMetric I M) (a b c : ℕ) (k : ℝ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g a b c (k • Φ) W =
      k • ccOperatorFieldComp (I := I) (M := M) g a b c Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [operatorFieldComposition_toSection]
  rw [show (k • ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toSection x =
      k • (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toSection x from rfl]
  rw [operatorFieldComposition_toSection, SmoothCcTensor.toSection_smul,
    ContMDiffSection.coe_smul, Pi.smul_apply]
  exact ContinuousLinearMap.smul_comp k
    (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
    (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x)
private def koszulOp
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  (1 / 2 : ℝ) •
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 2) +
      permCoeff (I := I) (M := M) g (finRotate 3) -
      permCoeff (I := I) (M := M) g (Equiv.swap (1 : Fin 3) 2))
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem symm_eq_self
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    (hS : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g S x u v =
        ccTensorBilin (I := I) g S x v u) :
    ccTensor02Symm (I := I) (M := M) g S = S := by
  have hswap :
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S = S := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
    rw [domDomCongrSection_unitModel]
    refine ContinuousMultilinearMap.ext fun v => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : ∀ u w : TangentSpace I x,
        unitModel (I := I) (M := M) g 2 S x ![u, w] =
          unitModel (I := I) (M := M) g 2 S x ![w, u] := by
      intro u w
      rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g S x u w,
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g S x w u]
      exact hS x u w
    have hveta :
        (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    exact hv (v 1) (v 0)
  have htwo : S + S = (2 : ℝ) • S := (two_smul ℝ S).symm
  unfold ccTensor02Symm
  rw [hswap, htwo, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit sigmaCompactSpace in
private theorem koszulOp_app
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u) :
    ccOperatorFieldComp (I := I) (M := M) g 0 3 3
        (koszulOp (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 T) =
      koszulCovecCc (I := I) g T := by
  have hs := symm_eq_self (I := I) (M := M) g T hT
  rw [koszulOp, app_smul_left, operatorFieldComposition_sub_left,
    operatorFieldComposition_add_left, permCoeff_app, permCoeff_app, permCoeff_app]
  rw [koszulCovecCc, symmSCovGrad3, hs]
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem raised_inner
    (g gm : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    gm.inner x (metricComparisonEndomorphismField (I := I) (M := M) g gm x v) w =
      g.inner x v w := by
  rw [metricComparisonEndomorphismField_apply, metricComparisonEndomorphism_apply]
  rw [inverseMetricSharpFib_inner (I := I) gm x
    (g0FlatCLM (I := I) g x v) w]
  rw [show cotangentToDualLinear (I := I) (x := x)
      (g0FlatCLM (I := I) g x v) w =
        cotangentToDual (I := I) (x := x)
          (g0FlatCLM (I := I) g x v) w from rfl]
  rw [cotangentToDual_g0FlatCLM]
private def connectionDifferenceLowOrderPermutation : Equiv.Perm (Fin 3) :=
  ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩
private def connectionDifferenceLowOrderOperator
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 3 3
    (permCoeff (I := I) (M := M) g connectionDifferenceLowOrderPermutation)
    (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
      (slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M) g gm))
      (koszulOp (I := I) (M := M) g))
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem connLower_unit
    (g gm : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 3 → E) :
    unitModel (I := I) (M := M) g 3
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gm) x v =
      g.inner x (PDE.DeTurck.connectionDifference (I := I) gm g x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2)) := by
  have h := connectionDifferenceLoweredCc_unitModel_apply' (I := I) (M := M) g gm x
    (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i))
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h

omit sigmaCompactSpace in
omit [NeZero (Module.finrank ℝ E)] in
private theorem koszulCc_unitModel_eq_connectionDifference_inner
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
    (x : M) (a b c : TangentSpace I x) :
    unitModel (I := I) (M := M) g 3 (koszulCovecCc (I := I) g T) x
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x c,
          tangentSpaceModelContinuousLinearEquiv (I := I) x a,
          tangentSpaceModelContinuousLinearEquiv (I := I) x b] =
      gm.inner x (PDE.DeTurck.connectionDifference (I := I) gm g x a b) c := by
  rw [koszulCovecCc_unitModel (I := I) g T x a b c]
  rw [connectionDifferenceInner_g1_eq_half_covGradSymmS
    (I := I) g gm T htie x a b c]
  rfl

omit sigmaCompactSpace in
omit [NeZero (Module.finrank ℝ E)] in
private theorem connLowerK
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    operatorFieldApply (I := I) (M := M) g 3 3
        (permCoeff (I := I) (M := M) g connectionDifferenceLowOrderPermutation)
        (operatorFieldApply (I := I) (M := M) g 3 3
          (slotInsertEndoCc (I := I) (M := M) g 2
            (metricComparisonEndomorphismField (I := I) (M := M) g gm))
          (koszulCovecCc (I := I) g T)) =
      metricLoweredConnectionDifferenceCoefficient (I := I) g gm := by
  rw [← operatorFieldComposition_zero_eq_operatorFieldApply, permCoeff_app]
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hv :
      (fun i => v (connectionDifferenceLowOrderPermutation i)) = ![v 2, v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  rw [unitModel, operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply,
    slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval]
  have hu :
      Function.update (![v 2, v 0, v 1] : Fin 3 → E) 0
          (tangentLinearMapToModel
            (metricComparisonEndomorphismField (I := I) (M := M) g gm x)
            ((![v 2, v 0, v 1] : Fin 3 → E) 0)) =
        ![tangentLinearMapToModel
            (metricComparisonEndomorphismField (I := I) (M := M) g gm x) (v 2),
          v 0, v 1] := by
    funext i
    fin_cases i <;> simp
  rw [hu]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (koszulCovecCc (I := I) g T).toSection x)
        (unitTensor (I := I) (M := M) x))
      ![tangentLinearMapToModel
          (metricComparisonEndomorphismField (I := I) (M := M) g gm x) (v 2),
        v 0, v 1] =
      unitModel (I := I) (M := M) g 3
        (koszulCovecCc (I := I) g T) x
        ![tangentLinearMapToModel
            (metricComparisonEndomorphismField (I := I) (M := M) g gm x) (v 2),
          v 0, v 1] from rfl]
  have hkoszul := koszulCc_unitModel_eq_connectionDifference_inner
    (I := I) (M := M) g gm T htie x
    ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
    ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1))
    (metricComparisonEndomorphismField (I := I) (M := M) g gm x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2)))
  simp only [ContinuousLinearEquiv.apply_symm_apply] at hkoszul
  rw [tangentLinearMapToModel_apply]
  rw [hkoszul]
  rw [gm.symm x
    (PDE.DeTurck.connectionDifference (I := I) gm g x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)))
    (metricComparisonEndomorphismField (I := I) (M := M) g gm x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2)))]
  rw [raised_inner (I := I) (M := M) g gm x, g.symm x]
  change g.inner x (PDE.DeTurck.connectionDifference (I := I) gm g x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2)) =
    unitModel (I := I) (M := M) g 3
      (metricLoweredConnectionDifferenceCoefficient (I := I) g gm) x v
  rw [connLower_unit (I := I) (M := M) g gm x v]
omit sigmaCompactSpace in
omit [NeZero (Module.finrank ℝ E)] in
private theorem connLowOp_app
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    ccOperatorFieldComp (I := I) (M := M) g 0 3 3
        (connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)
        (covGrad (I := I) (M := M) g 0 2 T) =
      metricLoweredConnectionDifferenceCoefficient (I := I) g gm := by
  rw [operatorFieldComposition_zero_eq_operatorFieldApply, connectionDifferenceLowOrderOperator, ← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc]
  rw [show operatorFieldApply (I := I) (M := M) g 3 3
      (koszulOp (I := I) (M := M) g)
      (covGrad (I := I) (M := M) g 0 2 T) =
        koszulCovecCc (I := I) g T by
      rw [← operatorFieldComposition_zero_eq_operatorFieldApply]
      exact koszulOp_app (I := I) (M := M) g T hT]
  exact connLowerK (I := I) (M := M) g gm T htie

private def ricciConnectionDifferenceDerivativeCyclicPermutation : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 3, 0], ![3, 0, 1, 2], by decide, by decide⟩
private def ricciConnectionDifferenceDerivativeFirstPairSwap : Equiv.Perm (Fin 4) :=
  ⟨![1, 0, 2, 3], ![1, 0, 2, 3], by decide, by decide⟩
private def gradRotate : Equiv.Perm (Fin 4) :=
  ⟨![0, 2, 3, 1], ![0, 3, 1, 2], by decide, by decide⟩
omit [NeZero (Module.finrank ℝ E)] in
omit sigmaCompactSpace in
private theorem ricciConnectionDifferenceCovariantDerivativeTensor_reindex
    (g gm : SmoothRiemannianMetric I M) :
    ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm =
      ccOperatorFieldComp (I := I) (M := M) g 0 4 4
        (permCoeff (I := I) (M := M) g ricciConnectionDifferenceDerivativeCyclicPermutation)
        (covGrad (I := I) (M := M) g 0 3
          (metricLoweredConnectionDifferenceCoefficient (I := I) g gm)) := by
  rw [permCoeff_app]
  let S : SmoothCcTensor g 0 3 := metricLoweredConnectionDifferenceCoefficient (I := I) g gm
  let S' : SmoothCcTensor g 0 3 :=
    domDomCongrSection (I := I) g (finRotate 3) S
  have hrel : ∀ (y : M) (d : Tensor0SSpace 0 I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
            S'.toSection y) d) =
        ContinuousMultilinearMap.domDomCongr (finRotate 3)
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
              S.toSection y) d)) := by
    intro y d
    rw [zero_eq_unit (I := I) (M := M) y d, map_smul, map_smul,
      Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_smul]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
          S'.toSection y) (unitTensor (I := I) (M := M) y)) =
      unitModel (I := I) (M := M) g 3 S' y from rfl]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
          S.toSection y) (unitTensor (I := I) (M := M) y)) =
      unitModel (I := I) (M := M) g 3 S y from rfl]
    rw [show S' = domDomCongrSection (I := I) g (finRotate 3) S from rfl,
      domDomCongrSection_unitModel]
    apply ContinuousMultilinearMap.ext
    intro v
    rw [smul_apply,
      ContinuousMultilinearMap.domDomCongr_apply,
      ContinuousMultilinearMap.domDomCongr_apply,
      smul_apply]
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [ricciConnectionDifferenceCovariantDerivativeTensor_unitModel (I := I) (M := M) g gm x v]
  rw [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hda :
      (fun i => v (ricciConnectionDifferenceDerivativeCyclicPermutation i)) = ![v 1, v 2, v 3, v 0] := by
    funext i
    fin_cases i <;> rfl
  rw [hda]
  have hnat := covGrad_rs_toModel_domDomCongr
    (I := I) (M := M) g 0 3 (finRotate 3) S S' hrel x
    (unitTensor (I := I) (M := M) x)
    (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
      ((![v 1, v 0, v 2, v 3] : Fin 4 → E) i))
  have hnat' :
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
            (covGrad (I := I) (M := M) g 0 3 S').toSection x)
            (unitTensor (I := I) (M := M) x)) ![v 1, v 0, v 2, v 3] =
        ContinuousMultilinearMap.domDomCongr
          (Equiv.Perm.decomposeFin.symm (0, finRotate 3))
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
              (covGrad (I := I) (M := M) g 0 3 S).toSection x)
              (unitTensor (I := I) (M := M) x))) ![v 1, v 0, v 2, v 3] := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hnat
  change unitModel (I := I) (M := M) g 4
      (covGrad (I := I) (M := M) g 0 3 S') x
        ![v 1, v 0, v 2, v 3] =
    unitModel (I := I) (M := M) g 4
      (covGrad (I := I) (M := M) g 0 3 S) x
        ![v 1, v 2, v 3, v 0]
  rw [show S' = domDomCongrSection (I := I) g (finRotate 3) S from rfl]
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
        (covGrad (I := I) (M := M) g 0 3
          (domDomCongrSection (I := I) g (finRotate 3) S)).toSection x)
        (unitTensor (I := I) (M := M) x)) _ = _
  rw [hnat']
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have hgrad :
      Equiv.Perm.decomposeFin.symm (0, finRotate 3) = gradRotate := by
    apply Equiv.ext
    intro i
    fin_cases i <;> decide
  rw [hgrad]
  congr 1
  funext i
  fin_cases i <;> rfl
private def ricciConnectionDerivativeCoefficient
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 4 4
    (permCoeff (I := I) (M := M) g ricciConnectionDifferenceDerivativeCyclicPermutation)
    (covGrad (I := I) (M := M) g 3 3
      (connectionDifferenceLowOrderOperator (I := I) (M := M) g gm))
private def ricciConnectionPrincipalCoefficient
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 4 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 4 4 4
    (permCoeff (I := I) (M := M) g ricciConnectionDifferenceDerivativeCyclicPermutation)
    (slotExtend (I := I) (M := M) g 3 3
      (connectionDifferenceLowOrderOperator (I := I) (M := M) g gm))
omit sigmaCompactSpace in
omit [NeZero (Module.finrank ℝ E)] in
private theorem ricciConnectionDifferenceCovariantDerivativeTensor_split
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm =
      ccOperatorFieldComp (I := I) (M := M) g 0 3 4
          (ricciConnectionDerivativeCoefficient (I := I) (M := M) g gm)
          (covGrad (I := I) (M := M) g 0 2 T) +
        ccOperatorFieldComp (I := I) (M := M) g 0 4 4
          (ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm)
          (iteratedCovGrad (I := I) g 0 2 2 T) := by
  rw [ricciConnectionDifferenceCovariantDerivativeTensor_reindex (I := I) (M := M) g gm]
  rw [← connLowOp_app (I := I) (M := M) g gm T hT htie]
  rw [covGrad_operatorFieldComposition_eq, operatorFieldComposition_add_right]
  rw [operatorFieldComposition_zero_eq_operatorFieldApply, operatorFieldComposition_zero_eq_operatorFieldApply, operatorFieldApplication_assoc]
  rw [operatorFieldComposition_zero_eq_operatorFieldApply, operatorFieldComposition_zero_eq_operatorFieldApply, operatorFieldApplication_assoc]
  simp only [ricciConnectionDerivativeCoefficient, ricciConnectionPrincipalCoefficient, operatorFieldComposition_zero_eq_operatorFieldApply,
    iteratedCovGrad_succ, iteratedCovGrad_zero]
private def ricciConnectionDifferenceDerivativeContractionMonomial
    (g gm : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) : SmoothCcTensor g 2 2 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 2 2
    (decompositionKernelContractionMonomialField (I := I) (M := M) g g G σ)
    (slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gm))
private def ricciConnectionDifferenceDerivativeContraction
    (g gm : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4) :
    SmoothCcTensor g 2 2 :=
  ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gm G ricciConnectionDifferenceDerivativeCyclicPermutation -
    ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gm G ricciConnectionDifferenceDerivativeFirstPairSwap
private def ricciConnectionDifferenceDerivativeMetricWeight
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 0 2 :=
  operatorFieldApply (I := I) (M := M) g 2 2
    (slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gm)) W
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem daWeight_cap
    (g gm : SmoothRiemannianMetric I M)
    (P W : SmoothCcTensor g 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g P y v w)
    {δ η : ℝ} (hδ_lt : δ < 1) (hδ : 0 ≤ δ)
    (hP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ)
    (hη : 0 ≤ η)
    (hW : ∀ (y : M) (v w : TangentSpace I y),
      |ccTensorBilin (I := I) g W y v w| ≤
        η * Real.sqrt (g.inner y v v) *
          Real.sqrt (g.inner y w w))
    (y : M) (v w : TangentSpace I y) :
    |Tensor0SSpace.toModel
        (ccTensorUnitValueSection (I := I) (M := M) g
          (ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm W) y)
        ![tangentSpaceModelContinuousLinearEquiv (I := I) y v,
          tangentSpaceModelContinuousLinearEquiv (I := I) y w]| ≤
      (η / (1 - δ)) * Real.sqrt (g.inner y v v) *
        Real.sqrt (g.inner y w w) := by
  have hval :
      Tensor0SSpace.toModel
          (ccTensorUnitValueSection (I := I) (M := M) g
            (ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm W) y)
          ![tangentSpaceModelContinuousLinearEquiv (I := I) y v,
            tangentSpaceModelContinuousLinearEquiv (I := I) y w] =
        ccTensorBilin (I := I) g W y
          (metricComparisonEndomorphismField (I := I) (M := M) g gm y v) w := by
    rw [show Tensor0SSpace.toModel
        (ccTensorUnitValueSection (I := I) (M := M) g
          (ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm W) y) =
      unitModel (I := I) (M := M) g 2
        (ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm W) y from rfl]
    simp only [ricciConnectionDifferenceDerivativeMetricWeight, unitModel, operatorFieldApplication_toSection,
      ContinuousLinearMap.comp_apply, slotInsertEndoCc_toSection,
      slotInsertEndoFib_apply_eval]
    have hu :
        Function.update
            ![tangentSpaceModelContinuousLinearEquiv (I := I) y v,
              tangentSpaceModelContinuousLinearEquiv (I := I) y w] 0
            (tangentLinearMapToModel
              (metricComparisonEndomorphismField (I := I) (M := M) g gm y)
              ((![tangentSpaceModelContinuousLinearEquiv (I := I) y v,
                tangentSpaceModelContinuousLinearEquiv (I := I) y w] : Fin 2 → E) 0)) =
          ![tangentSpaceModelContinuousLinearEquiv (I := I) y
              (metricComparisonEndomorphismField (I := I) (M := M) g gm y v),
            tangentSpaceModelContinuousLinearEquiv (I := I) y w] := by
      funext i
      fin_cases i <;> simp [tangentLinearMapToModel_apply]
    rw [hu]
    change unitModel (I := I) (M := M) g 2 W y
        ![tangentSpaceModelContinuousLinearEquiv (I := I) y
            (metricComparisonEndomorphismField (I := I) (M := M) g gm y v),
          tangentSpaceModelContinuousLinearEquiv (I := I) y w] = _
    exact unitModel_eq_ccTensorBilin_local (I := I) (M := M) g W y
      (metricComparisonEndomorphismField (I := I) (M := M) g gm y v) w
  have hinv := sqrt_inner_metricComparisonEndomorphism_le
    (I := I) (M := M) g gm
    (ccTensorBilinSymm (I := I) g P) htie hδ_lt hδ hP y v
  calc
    _ = |ccTensorBilin (I := I) g W y
          (metricComparisonEndomorphismField (I := I) (M := M) g gm y v) w| := by
      rw [hval]
    _ ≤ η * Real.sqrt (g.inner y
          (metricComparisonEndomorphismField (I := I) (M := M) g gm y v)
          (metricComparisonEndomorphismField (I := I) (M := M) g gm y v)) *
        Real.sqrt (g.inner y w w) := hW _ _ _
    _ ≤ η * ((1 / (1 - δ)) * Real.sqrt (g.inner y v v)) *
        Real.sqrt (g.inner y w w) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinv hη) (Real.sqrt_nonneg _)
    _ = (η / (1 - δ)) * Real.sqrt (g.inner y v v) *
        Real.sqrt (g.inner y w w) := by ring
private def ricciConnectionDifferenceDerivativeTransposedMonomial
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (σ : Equiv.Perm (Fin 4)) : SmoothCcTensor g 4 2 :=
  curvatureDecompositionMonomialCoeffField (I := I) (M := M) g g
    (ccTensorUnitValueSection (I := I) (M := M) g
      (ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm W))
    (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g
      (ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm W)) σ
omit [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem daMono_cap
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ : 0 ≤ δ)
    (hTδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (σ : Equiv.Perm (Fin 4)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        ((ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hTδ hδZ s) T σ).toSection x) ≤
      (deTurckArmFibreConst (Module.finrank ℝ E) *
        (δ / (1 - δ))) ^ 2 := by
  let gm := metricPerturbationPath (I := I) g T 0 hTδ hδZ s
  have hsmem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w =
        g.inner y v w +
          ccTensorBilinSymm (I := I) g
            (convexPerturbation (I := I) g T 0 s) y v w :=
    fun y v w => metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hTδ hδZ hsmem y v w
  have hP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (convexPerturbation (I := I) g T 0 s)) δ := by
    convert convexPerturbation_gFibreOpBound
      (I := I) (M := M) g T 0 hTδ hδZ hs.1 hs.2 using 1
    all_goals ring
  have hTcap : ∀ (y : M) (v w : TangentSpace I y),
      |ccTensorBilin (I := I) g T y v w| ≤
        δ * Real.sqrt (g.inner y v v) *
          Real.sqrt (g.inner y w w) := by
    intro y v w
    rw [show ccTensorBilin (I := I) g T y v w =
        ccTensorBilinSymm (I := I) g T y v w by
      rw [ccTensorBilinSymm_apply, ← hT y v w]
      ring]
    exact hTδ y v w
  have hratio : 0 ≤ δ / (1 - δ) :=
    div_nonneg hδ (by linarith)
  have hweight := daWeight_cap (I := I) (M := M)
    g gm (convexPerturbation (I := I) g T 0 s) T
    htie hδ_lt hδ hP hδ hTcap
  have hzero_app : ∀ (y : M) (v w : TangentSpace I y),
      ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2) y v w = 0 := by
    intro y v w
    have hzero : (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
      (zero_smul ℝ _).symm
    rw [hzero, ccTensorBilinSymm_smul]
    ring
  have htie0 : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w =
        g.inner y v w +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) y v w := by
    intro y v w
    rw [hzero_app, add_zero]
  have hzero_bound : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) 0 := by
    intro y v w
    rw [hzero_app]
    simp only [abs_zero, zero_mul, le_refl]
  rw [ricciConnectionDifferenceDerivativeTransposedMonomial, curvatureDecompositionMonomialCoeffField_toSection]
  simpa only [gm, sub_zero, one_pow, div_one] using
    (riemannianFiberNormSq_curvatureDecompositionMonomialBiContrFib_le
      (I := I) (M := M) g g (0 : SmoothCcTensor g 0 2)
      htie0 (δ := 0) (by norm_num)
      hzero_bound
      (ccTensorUnitValueSection (I := I) (M := M) g
        (ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm T))
      hratio hweight σ x)
private def ricciConnectionDifferenceDerivativeTransposedCoefficient
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 4 2 :=
  ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M) g gm W ricciConnectionDifferenceDerivativeCyclicPermutation -
    ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M) g gm W ricciConnectionDifferenceDerivativeFirstPairSwap
omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem ricciConnectionDifferenceDerivativeTransposedCoefficient_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ : 0 ≤ δ)
    (hTδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        ((ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hTδ hδZ s) T).toSection x) ≤
      (2 * deTurckArmFibreConst (Module.finrank ℝ E) *
        (δ / (1 - δ))) ^ 2 := by
  simp only [ricciConnectionDifferenceDerivativeTransposedCoefficient, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply]
  refine le_trans
    (riemannianFiberNormSq_sub_le (I := I) (M := M)
      g 4 2 x _ _) ?_
  have hA := daMono_cap (I := I) (M := M) g T hT
    hδ_lt hδ hTδ hδZ s hs ricciConnectionDifferenceDerivativeCyclicPermutation x
  have hB := daMono_cap (I := I) (M := M) g T hT
    hδ_lt hδ hTδ hδZ s hs ricciConnectionDifferenceDerivativeFirstPairSwap x
  nlinarith only [hA, hB]
private theorem fullSlot_cap
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        {δ : ℝ}, δ ≤ 1 / 3 → 0 ≤ δ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ →
        (∀ (y : M) (v w : TangentSpace I y),
          gm.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g P y v w) →
        ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 3 3 x
            ((slotInsertEndoCc (I := I) (M := M) g 2
              (metricComparisonEndomorphismField (I := I) (M := M) g gm)).toSection x) ≤ K := by
  obtain ⟨C, hC_nn, hC⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_metricComparisonDifferenceEndomorphismField_diagonalProductGrid_le
      (I := I) (M := M) g (δ₀ := (1 : ℝ) / 3) (by norm_num)
  obtain ⟨K0, hK0, hK0b⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g 3 3
      (slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M) g g))
  let n : ℝ := Module.finrank ℝ E
  let K := 2 * (n ^ 2 * C 0 + K0)
  refine ⟨K, by
    exact mul_nonneg (by norm_num)
      (add_nonneg
        (mul_nonneg (sq_nonneg n) (hC_nn 0)) hK0), ?_⟩
  intro gm P δ hδ_le hδ hP htie x
  have hD0 := hC gm P htie hδ_le hδ hP 0 x
  rw [show (∑ q ∈ Finset.range (0 + 1),
      ∑ e ∈ Finset.Nat.antidiagonalTuple q 0,
        ∏ m : Fin q,
          riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)) =
      DifferentialGeometry.Combinatorics.antidiagonalTupleGrid
        (fun j => riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
          ((iteratedCovGrad (I := I) g 0 2 j P).toSection x)) 0 from rfl,
    DifferentialGeometry.Combinatorics.antidiagonalTupleGrid_zero,
    iteratedCovGrad_zero, mul_one] at hD0
  have hD2 := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo
    (I := I) (M := M) g 2
    (metricComparisonDifferenceEndomorphismField (I := I) g gm) 0 x
  simp only [iteratedCovGrad_zero, Nat.reduceAdd] at hD2
  have hdiff :
      riemannianFiberNormSq (I := I) (M := M) g 3 3 x
          ((slotInsertEndoCc (I := I) (M := M) g 2
            (metricComparisonDifferenceEndomorphismField (I := I) g gm)).toSection x) ≤
        n ^ 2 * C 0 := by
    calc
      _ ≤ n ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 1 1 x
          ((slotInsertEndoCc (I := I) (M := M) g 0
            (metricComparisonDifferenceEndomorphismField (I := I) g gm)).toSection x) := by
        simpa only [n] using hD2
      _ ≤ n ^ 2 * C 0 := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Nat.add_zero] using hD0) (sq_nonneg n)
  have hfull :
      metricComparisonEndomorphismField (I := I) (M := M) g gm =
        metricComparisonDifferenceEndomorphismField (I := I) g gm +
          metricComparisonEndomorphismField (I := I) (M := M) g g := by
    apply ContMDiffSection.ext
    intro y
    apply ContinuousLinearMap.ext
    intro v
    change metricComparisonEndomorphism (I := I) g gm y v =
      metricComparisonDifferenceEndomorphism (I := I) g gm y v +
        metricComparisonEndomorphism (I := I) g g y v
    rw [show metricComparisonEndomorphism (I := I) g g y v = v by
      rw [metricComparisonEndomorphism_apply, inverseMetricSharpFib_g0FlatCLM]]
    exact metricComparisonEndomorphism_eq_diff_add_id (I := I) g gm y v
  rw [hfull, slotInsertEndoCc_add, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_add, Pi.add_apply]
  refine le_trans
    (riemannianFiberNormSq_add_le (I := I) (M := M)
      g 3 3 x _ _) ?_
  have hbase := hK0b x
  dsimp only [K]
  nlinarith only [hdiff, hbase]
private theorem dagTop_cap
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2) {δ : ℝ},
        δ ≤ 1 / 3 → 0 ≤ δ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ →
        (∀ (y : M) (v w : TangentSpace I y),
          gm.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g P y v w) →
        ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 4 4 x
          ((ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm).toSection x) ≤ K := by
  obtain ⟨KF, hKF, hFb⟩ := fullSlot_cap (I := I) (M := M) g
  obtain ⟨KK, hKK, hKb⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g 3 3 (koszulOp (I := I) (M := M) g)
  obtain ⟨KP3, hKP3, hP3b⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g 3 3
      (permCoeff (I := I) (M := M) g connectionDifferenceLowOrderPermutation)
  obtain ⟨KP4, hKP4, hP4b⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g 4 4
      (permCoeff (I := I) (M := M) g ricciConnectionDifferenceDerivativeCyclicPermutation)
  let n : ℝ := Module.finrank ℝ E
  let K := KP4 * (n * (KP3 * (KF * KK)))
  refine ⟨K, mul_nonneg hKP4
    (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg hKP3 (mul_nonneg hKF hKK))), ?_⟩
  intro gm P δ hδ_le hδ hP htie x
  have hfull := hFb gm P hδ_le hδ hP htie x
  have hinner := riemannianFiberNormSq_compRS_le_mul
    (I := I) (M := M) g 3 3 3 x
    ((slotInsertEndoCc (I := I) (M := M) g 2
      (metricComparisonEndomorphismField (I := I) (M := M) g gm)).toSection x)
    ((koszulOp (I := I) (M := M) g).toSection x)
  rw [← operatorFieldComposition_toSection] at hinner
  have hinner' :
      riemannianFiberNormSq (I := I) (M := M) g 3 3 x
          ((ccOperatorFieldComp (I := I) (M := M) g 3 3 3
            (slotInsertEndoCc (I := I) (M := M) g 2
              (metricComparisonEndomorphismField (I := I) (M := M) g gm))
            (koszulOp (I := I) (M := M) g)).toSection x) ≤ KF * KK :=
    hinner.trans (mul_le_mul (hfull) (hKb x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 3 3 x _)
      hKF)
  have hconn := riemannianFiberNormSq_compRS_le_mul
    (I := I) (M := M) g 3 3 3 x
    ((permCoeff (I := I) (M := M) g connectionDifferenceLowOrderPermutation).toSection x)
    ((ccOperatorFieldComp (I := I) (M := M) g 3 3 3
      (slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M) g gm))
      (koszulOp (I := I) (M := M) g)).toSection x)
  rw [← operatorFieldComposition_toSection] at hconn
  have hconn' := hconn.trans
    (mul_le_mul (hP3b x) hinner'
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 3 3 x _) hKP3)
  have hslot := riemannianFiberNormSq_slotExtend_eq (I := I) (M := M)
    g 3 3 (connectionDifferenceLowOrderOperator (I := I) (M := M) g gm) x
  have hout := riemannianFiberNormSq_compRS_le_mul
    (I := I) (M := M) g 4 4 4 x
    ((permCoeff (I := I) (M := M) g ricciConnectionDifferenceDerivativeCyclicPermutation).toSection x)
    ((slotExtend (I := I) (M := M) g 3 3
      (connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)).toSection x)
  rw [← operatorFieldComposition_toSection] at hout
  rw [hslot] at hout
  have hout' :
      riemannianFiberNormSq (I := I) (M := M) g 4 4 x
          ((ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm).toSection x) ≤
        riemannianFiberNormSq (I := I) (M := M) g 4 4 x
            ((permCoeff (I := I) (M := M) g ricciConnectionDifferenceDerivativeCyclicPermutation).toSection x) *
          ((Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g 3 3 x
              ((connectionDifferenceLowOrderOperator (I := I) (M := M) g gm).toSection x)) := by
    simpa only [ricciConnectionPrincipalCoefficient] using hout
  refine hout'.trans ?_
  dsimp only [K, n]
  exact mul_le_mul (hP4b x)
    (mul_le_mul_of_nonneg_left hconn' (Nat.cast_nonneg _))
    (mul_nonneg (Nat.cast_nonneg _)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 3 3 x _)) hKP4

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem mono_trans
    (g : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (decompositionKernelContractionMonomialField
          (I := I) (M := M) g g G σ) W =
      operatorFieldApply (I := I) (M := M) g 4 2
        (curvatureDecompositionMonomialCoeffField (I := I) (M := M) g g
          (ccTensorUnitValueSection (I := I) (M := M) g W)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g W) σ) G := by
  classical
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  rw [unitModel, unitModel]
  refine congrArg Tensor0SSpace.toModel ?_
  change
    (decompositionKernelContractionMonomialBiContrFib (I := I) (M := M) g
      (ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g G) σ x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        W.toSection x) (unitTensor (I := I) (M := M) x)) =
    (curvatureDecompositionMonomialBiContrFib (I := I) (M := M) g
      (ccTensorUnitValueSection (I := I) (M := M) g W) σ x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
        G.toSection x) (unitTensor (I := I) (M := M) x))
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [decompositionKernelContractionMonomialBiContrFib,
    curvatureDecompositionMonomialOrthonormalFrameBiContraction,
    decompositionKernelContractionMonomialFibFixedFrame_toModel,
    curvatureDecompositionMonomialBiContrFib,
    curvatureActionMonomialTrace,
    curvatureDecompositionMonomialFibFixedFrame_toModel]
  rfl

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem daMono_trans
    (g gm : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gm G σ) W =
      operatorFieldApply (I := I) (M := M) g 4 2
        (ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M) g gm W σ) G := by
  rw [ricciConnectionDifferenceDerivativeContractionMonomial, ← operatorFieldApplication_assoc]
  exact mono_trans (I := I) (M := M) g G σ
    (ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm W)

omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
omit sigmaCompactSpace in
private theorem daContr_trans
    (g gm : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ricciConnectionDifferenceDerivativeContraction (I := I) (M := M) g gm G) W =
      operatorFieldApply (I := I) (M := M) g 4 2
        (ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm W) G := by
  rw [ricciConnectionDifferenceDerivativeContraction, ricciConnectionDifferenceDerivativeTransposedCoefficient, operatorFieldApplication_sub_left, operatorFieldApplication_sub_left,
    daMono_trans, daMono_trans]

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem daMono_eval
    (g gm : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) (W : SmoothCcTensor g 0 2)
    (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2
          (ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gm G σ) W) x v =
      ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g 2 W x
              ![tangentSpaceModelContinuousLinearEquiv (I := I) x
                  (metricComparisonEndomorphismField (I := I) (M := M) g gm x
                    (smoothOrthoFrame (I := I) g x a x)),
                tangentSpaceModelContinuousLinearEquiv (I := I) x
                  (smoothOrthoFrame (I := I) g x b x)] *
            unitModel (I := I) (M := M) g 4 G x
              (fun i =>
                (![tangentSpaceModelContinuousLinearEquiv (I := I) x
                      (smoothOrthoFrame (I := I) g x a x),
                    tangentSpaceModelContinuousLinearEquiv (I := I) x
                      (smoothOrthoFrame (I := I) g x b x),
                    v 0, v 1] : Fin 4 → E) (σ i)) := by
  classical
  rw [ricciConnectionDifferenceDerivativeContractionMonomial, ← operatorFieldApplication_assoc (I := I) (M := M) g 2 2 2]
  rw [unitModel, operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply,
    decompositionKernelContractionMonomialField_toSection]
  change Tensor0SSpace.toModel
      (curvatureDecompositionMonomialFrameContraction
        (I := I) (M := M)
        (ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g G) σ
        (smoothOrthoFrame (I := I) g x) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (operatorFieldApply (I := I) (M := M) g 2 2
            (slotInsertEndoCc (I := I) (M := M) g 1
              (metricComparisonEndomorphismField (I := I) (M := M) g gm)) W).toSection x)
          (unitTensor (I := I) (M := M) x))) v = _
  rw [decompositionKernelContractionMonomialFibFixedFrame_toModel]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  · change unitModel (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (slotInsertEndoCc (I := I) (M := M) g 1
              (metricComparisonEndomorphismField (I := I) (M := M) g gm)) W) x
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g x a x),
            tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g x b x)] = _
    rw [unitModel, operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply,
      slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval]
    have hv :
        Function.update
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) g x a x),
              tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) g x b x)]
            0
            (tangentLinearMapToModel
              (metricComparisonEndomorphismField (I := I) (M := M) g gm x)
              (![tangentSpaceModelContinuousLinearEquiv (I := I) x
                  (smoothOrthoFrame (I := I) g x a x),
                tangentSpaceModelContinuousLinearEquiv (I := I) x
                  (smoothOrthoFrame (I := I) g x b x)] 0)) =
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x
              (metricComparisonEndomorphismField (I := I) (M := M) g gm x
                (smoothOrthoFrame (I := I) g x a x)),
            tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g x b x)] := by
      funext i
      fin_cases i <;> simp [tangentLinearMapToModel_apply]
    rw [hv]
    rfl
  · congr 1
    funext i
    congr 1
    funext j
    fin_cases j <;> rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem unit_sub
    (g : SmoothRiemannianMetric I M) (A B : SmoothCcTensor g 0 2)
    (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2 (A - B) x v =
      unitModel (I := I) (M := M) g 2 A x v -
        unitModel (I := I) (M := M) g 2 B x v := by
  have hfun : unitModel (I := I) (M := M) g 2 (A - B) x =
      unitModel (I := I) (M := M) g 2 A x -
        unitModel (I := I) (M := M) g 2 B x := by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      sub_apply, Tensor0SSpace.toModel_sub]
  rw [hfun, sub_apply]

omit sigmaCompactSpace in
private theorem ricciCovariantDerivativeConnectionDifference_action
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (hW : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g W x u v =
        ccTensorBilin (I := I) g W x v u) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ricciCovariantDerivativeConnectionDifferenceArm (I := I) (M := M) g gm) W =
      operatorFieldApply (I := I) (M := M) g 2 2
        (ricciConnectionDifferenceDerivativeContraction (I := I) (M := M) g gm
          (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm)) W := by
  classical
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  refine ContinuousMultilinearMap.ext fun v => ?_
  have hexp := ricciCovariantDerivativeConnectionDifference_finiteSum_expansion
    (I := I) (M := M) g gm W hW x
      (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i))
  simp only [ContinuousLinearEquiv.apply_symm_apply] at hexp
  rw [hexp]
  simp only [ricciConnectionDifferenceDerivativeContraction, operatorFieldApplication_sub_left]
  rw [unit_sub (I := I) (M := M) g]
  rw [daMono_eval (I := I) (M := M) g gm _ ricciConnectionDifferenceDerivativeCyclicPermutation W x v,
    daMono_eval (I := I) (M := M) g gm _ ricciConnectionDifferenceDerivativeFirstPairSwap W x v]
  nth_rewrite 1 [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hA :
      (fun i =>
        (![tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g x p x),
            tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g x r x), v 0, v 1] :
          Fin 4 → E) (ricciConnectionDifferenceDerivativeCyclicPermutation i)) =
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x
            (smoothOrthoFrame (I := I) g x r x), v 0, v 1,
          tangentSpaceModelContinuousLinearEquiv (I := I) x
            (smoothOrthoFrame (I := I) g x p x)] := by
    funext i
    fin_cases i <;> rfl
  have hB :
      (fun i =>
        (![tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g x p x),
            tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g x r x), v 0, v 1] :
          Fin 4 → E) (ricciConnectionDifferenceDerivativeFirstPairSwap i)) =
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x
            (smoothOrthoFrame (I := I) g x r x),
          tangentSpaceModelContinuousLinearEquiv (I := I) x
            (smoothOrthoFrame (I := I) g x p x), v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hA, hB]
  ring

private def ricciCovariantDerivativeConnectionDifferenceLowOrder
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 2 2 :=
  ricciConnectionDifferenceDerivativeContraction (I := I) (M := M) g gm
    (ccOperatorFieldComp (I := I) (M := M) g 0 3 4
      (ricciConnectionDerivativeCoefficient (I := I) (M := M) g gm)
      (covGrad (I := I) (M := M) g 0 2 T))

private def ricciCovariantDerivativeConnectionDifferenceTopOrder
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 4 2 :=
  ccOperatorFieldComp (I := I) (M := M) g 4 4 2
    (ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm T)
    (ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm)

omit sigmaCompactSpace in
private theorem ricciCovariantDerivativeConnectionDifference_decomposition
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (hW : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g W x u v =
        ccTensorBilin (I := I) g W x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ricciCovariantDerivativeConnectionDifferenceArm (I := I) (M := M) g gm) W =
      operatorFieldApply (I := I) (M := M) g 2 2
          (ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gm P) W +
        operatorFieldApply (I := I) (M := M) g 4 2
          (ricciCovariantDerivativeConnectionDifferenceTopOrder (I := I) (M := M) g gm W)
          (iteratedCovGrad (I := I) g 0 2 2 P) := by
  rw [ricciCovariantDerivativeConnectionDifference_action (I := I) (M := M) g gm W hW]
  rw [daContr_trans]
  rw [ricciConnectionDifferenceCovariantDerivativeTensor_split (I := I) (M := M) g gm P hP htie]
  rw [operatorFieldApplication_add_right]
  rw [← daContr_trans]
  simp only [ricciCovariantDerivativeConnectionDifferenceLowOrder, ricciCovariantDerivativeConnectionDifferenceTopOrder]
  simp only [operatorFieldComposition_zero_eq_operatorFieldApply]
  rw [← operatorFieldApplication_assoc]

private def ricciConnectionDifferenceLowOrderCoefficient
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 2 2 :=
  ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gm +
    ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gm T

private def ricciConnectionDifferenceTopOrderCoefficient
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 4 2 :=
  ricciCovariantDerivativeConnectionDifferenceTopOrder (I := I) (M := M) g gm T

private theorem ricciTop_cap
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ}, δ ≤ 1 / 3 → 0 ≤ δ →
        ∀ (hTδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
          (hδZ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g
              (0 : SmoothCcTensor g 0 2)) δ)
          (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            ((ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hTδ hδZ s) T).toSection x) ≤
          (K * (δ / (1 - δ))) ^ 2 := by
  obtain ⟨KD, hKD, hDb⟩ := dagTop_cap (I := I) (M := M) g
  let K := 2 * deTurckArmFibreConst (Module.finrank ℝ E) * (1 + KD)
  refine ⟨K, mul_nonneg
    (mul_nonneg (by norm_num)
      (by
        exact Real.sqrt_nonneg _ :
          0 ≤ deTurckArmFibreConst (Module.finrank ℝ E)))
    (by linarith), ?_⟩
  intro T hT δ hδ_le hδ hTδ hδZ s hs x
  let gm := metricPerturbationPath (I := I) g T 0 hTδ hδZ s
  let P := convexPerturbation (I := I) g T 0 s
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hsmem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g P y v w :=
    fun y v w => metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hTδ hδZ hsmem y v w
  have hP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    convert convexPerturbation_gFibreOpBound
      (I := I) (M := M) g T 0 hTδ hδZ hs.1 hs.2 using 1
    all_goals ring
  have hA := ricciConnectionDifferenceDerivativeTransposedCoefficient_fiberNormSq_le (I := I) (M := M) g T hT
    hδ_lt hδ hTδ hδZ s hs x
  have hD := hDb gm P hδ_le hδ hP htie x
  have hc := riemannianFiberNormSq_compRS_le_mul
    (I := I) (M := M) g 4 4 2 x
    ((ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm T).toSection x)
    ((ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm).toSection x)
  rw [← operatorFieldComposition_toSection] at hc
  have hprod := mul_le_mul hA hD
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g 4 4 x _)
    (sq_nonneg (2 * deTurckArmFibreConst (Module.finrank ℝ E) *
      (δ / (1 - δ))))
  calc
    _ ≤ riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        ((ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm T).toSection x) *
      riemannianFiberNormSq (I := I) (M := M) g 4 4 x
        ((ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm).toSection x) := by
      simpa only [ricciConnectionDifferenceTopOrderCoefficient, ricciCovariantDerivativeConnectionDifferenceTopOrder, gm] using hc
    _ ≤ (2 * deTurckArmFibreConst (Module.finrank ℝ E) *
          (δ / (1 - δ))) ^ 2 * KD := hprod
    _ ≤ (2 * deTurckArmFibreConst (Module.finrank ℝ E) *
          (δ / (1 - δ))) ^ 2 * (1 + KD) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      nlinarith only [hKD]
    _ = (K * (δ / (1 - δ))) ^ 2 := by
      simp only [K]
      ring

private def ricciConnectionDifferenceSecondDerivativeContraction
    (g gm : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 2 2 :=
  ricciConnectionDifferenceDerivativeContraction (I := I) (M := M) g gm
    (ccOperatorFieldComp (I := I) (M := M) g 0 4 4
      (ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm)
      (iteratedCovGrad (I := I) g 0 2 2 P))

private def reducedRicciConnectionDifferenceLowOrderCoefficient
    (g gm : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 2 2 :=
  ccInputSlotSymm (I := I) (M := M) g
    (linearizedRicciConnectionDifferenceOrder0CoeffField
        (I := I) (M := M) g gm -
      ricciConnectionDifferenceSecondDerivativeContraction (I := I) (M := M) g gm P)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem ccInputSlotSymm_app
    (g : SmoothRiemannianMetric I M) (C : SmoothCcTensor g 2 2)
    (W : SmoothCcTensor g 0 2)
    (hW : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g W x u v =
        ccTensorBilin (I := I) g W x v u) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ccInputSlotSymm (I := I) (M := M) g C) W =
      operatorFieldApply (I := I) (M := M) g 2 2 C W := by
  have hswap :
      operatorFieldApply (I := I) (M := M) g 2 2
          (ccInputSlotSwapField (I := I) (M := M) g) W = W := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    rw [unitModel, operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply,
      ccSlotSwapField_toSection]
    change Tensor0SSpace.toModel
        (slotSwapFib (I := I) (M := M) x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))) v =
      unitModel (I := I) (M := M) g 2 W x v
    rw [slotSwapFib_apply,
      Tensor0SSpace.toModel_ofModel,
      ContinuousMultilinearMap.domDomCongr_apply]
    have hv :
        (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hv' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    conv_rhs => rw [hv']
    have hunit :
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x)) =
          unitModel (I := I) (M := M) g 2 W x := rfl
    rw [hunit]
    have hleft := unitModel_eq_ccTensorBilin_local (I := I) (M := M) g W x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
    have hright := unitModel_eq_ccTensorBilin_local (I := I) (M := M) g W x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1))
    change unitModel (I := I) (M := M) g 2 W x
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)),
          tangentSpaceModelContinuousLinearEquiv (I := I) x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))] = _ at hleft
    change unitModel (I := I) (M := M) g 2 W x
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)),
          tangentSpaceModelContinuousLinearEquiv (I := I) x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1))] = _ at hright
    simp only [ContinuousLinearEquiv.apply_symm_apply] at hleft hright
    rw [hleft, hright]
    exact hW x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
  unfold ccInputSlotSymm
  rw [operatorFieldApplication_smul_left, operatorFieldApplication_add_left, ← operatorFieldApplication_assoc, hswap]
  module

omit sigmaCompactSpace in
private theorem ricciConnectionDifference_decomposition
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (hW : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g W x u v =
        ccTensorBilin (I := I) g W x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (linearizedRicciConnectionDifferenceOrder0CoeffField
          (I := I) (M := M) g gm) W =
      operatorFieldApply (I := I) (M := M) g 2 2
          (ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P) W +
        operatorFieldApply (I := I) (M := M) g 4 2
          (ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm W)
          (iteratedCovGrad (I := I) g 0 2 2 P) := by
  rw [ricciCoeff_split, operatorFieldApplication_add_left]
  rw [ricciCovariantDerivativeConnectionDifference_decomposition (I := I) (M := M) g gm P W hP hW htie]
  simp only [ricciConnectionDifferenceLowOrderCoefficient, ricciConnectionDifferenceTopOrderCoefficient, operatorFieldApplication_add_left]
  module

omit sigmaCompactSpace in
private theorem safeLow_action
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (hW : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g W x u v =
        ccTensorBilin (I := I) g W x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (reducedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P) W =
      operatorFieldApply (I := I) (M := M) g 2 2
        (ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P) W := by
  rw [reducedRicciConnectionDifferenceLowOrderCoefficient, ccInputSlotSymm_app (I := I) (M := M) g _ W hW,
    operatorFieldApplication_sub_left]
  have hconn := ricciConnectionDifference_decomposition (I := I) (M := M)
    g gm P W hP hW htie
  have htop :
      operatorFieldApply (I := I) (M := M) g 2 2
          (ricciConnectionDifferenceSecondDerivativeContraction (I := I) (M := M) g gm P) W =
        operatorFieldApply (I := I) (M := M) g 4 2
          (ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm W)
          (iteratedCovGrad (I := I) g 0 2 2 P) := by
    rw [ricciConnectionDifferenceSecondDerivativeContraction, daContr_trans, operatorFieldComposition_zero_eq_operatorFieldApply, operatorFieldApplication_assoc]
    rfl
  rw [htop, hconn]
  module

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem ccSwap_app
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ccInputSlotSwapField (I := I) (M := M) g) W =
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) W := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  rw [domDomCongrSection_unitModel]
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [unitModel, operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply,
    ccSlotSwapField_toSection]
  change Tensor0SSpace.toModel
      (slotSwapFib (I := I) (M := M) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x))) v =
    (ContinuousMultilinearMap.domDomCongr
      (Equiv.swap (0 : Fin 2) 1)
      (unitModel (I := I) (M := M) g 2 W x)) v
  rw [slotSwapFib_apply, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem ccInputSlotSymm_action
    (g : SmoothRiemannianMetric I M) (C : SmoothCcTensor g 2 2)
    (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ccInputSlotSymm (I := I) (M := M) g C) W =
      operatorFieldApply (I := I) (M := M) g 2 2 C
        (ccTensor02Symm (I := I) (M := M) g W) := by
  unfold ccInputSlotSymm
  rw [operatorFieldApplication_smul_left, operatorFieldApplication_add_left, ← operatorFieldApplication_assoc,
    ccSwap_app (I := I) (M := M) g W]
  unfold ccTensor02Symm
  rw [operatorFieldApplication_smul_right, operatorFieldApplication_add_right]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem cc22_ext
    (g : SmoothRiemannianMetric I M) (C D : SmoothCcTensor g 2 2)
    (h : ∀ W : SmoothCcTensor g 0 2,
      operatorFieldApply (I := I) (M := M) g 2 2 C W =
        operatorFieldApply (I := I) (M := M) g 2 2 D W) :
    C = D := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext fun x => ?_
  refine tensorRSSpace_ext 2 2 x fun u => ?_
  let V : TensorRSSpace 0 2 I x :=
    (show TensorRSSpace 0 2 I x from
      ((MixedSection.eval₀ (F := E)
        (E := (TangentSpace I : M → Type _)) x).smulRight u))
  obtain ⟨σW, hσW⟩ := ContMDiffSection.exists_eq_at
    (I := I) (n := (⊤ : ℕ∞)) (F := TensorRSModel 0 2 ℝ E)
    (V := fun z : M => TensorRSSpace 0 2 I z) x V
  let W₀ : SmoothCcTensor g 0 2 :=
    { toSection := σW
      hasCompactSupport := HasCompactSupport.of_compactSpace _ }
  have h1 : (operatorFieldApply (I := I) (M := M) g 2 2 C W₀).toSection x =
      (operatorFieldApply (I := I) (M := M) g 2 2 D W₀).toSection x := by
    rw [h W₀]
  have h2 : (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        C.toSection x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        W₀.toSection x) (unitTensor (I := I) (M := M) x)) =
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        D.toSection x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        W₀.toSection x) (unitTensor (I := I) (M := M) x)) := by
    exact congrArg
      (fun Z : TensorRSSpace 0 2 I x =>
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from Z)
          (unitTensor (I := I) (M := M) x)) h1
  have hWval :
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        W₀.toSection x) (unitTensor (I := I) (M := M) x) = u := by
    rw [show W₀.toSection x = V from hσW]
    change ((MixedSection.eval₀ (F := E)
        (E := (TangentSpace I : M → Type _)) x).smulRight u)
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) 1) = u
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rwa [hWval] at h2

private def symmetrizedRicciConnectionDifferenceLowOrderCoefficient
    (g gm : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 2 2 :=
  ccInputSlotSymm (I := I) (M := M) g
    (ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P)

omit sigmaCompactSpace in
private theorem ricciGood_eq_safe
    (g gm : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P =
      reducedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P := by
  apply cc22_ext (I := I) (M := M) g
  intro W
  rw [symmetrizedRicciConnectionDifferenceLowOrderCoefficient, ccInputSlotSymm_action]
  rw [reducedRicciConnectionDifferenceLowOrderCoefficient, ccInputSlotSymm_action]
  let SW := symmS (I := I) (M := M) g W
  have hSW : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g SW x u v =
        ccTensorBilin (I := I) g SW x v u := by
    intro x u v
    simp only [SW, ccTensorBilin_symmS, ccTensorBilinSymm_apply]
    ring
  have hs := safeLow_action (I := I) (M := M)
    g gm P SW hP hSW htie
  rw [reducedRicciConnectionDifferenceLowOrderCoefficient,
    ccInputSlotSymm_app (I := I) (M := M) g _ SW hSW] at hs
  exact hs.symm

private abbrev JointRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : Set ℝ)
    (A : ℝ → SmoothCcTensor g r s) : Prop :=
  ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
    (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
    (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
      (E := fun x : M => TensorRSSpace r s I x) p.1
      ((A p.2).toSection p.1))
    ((Set.univ : Set M) ×ˢ S)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem joint_const
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {S : Set ℝ}
    (A : SmoothCcTensor g r s) :
    JointRS (I := I) g r s S (fun _ => A) := by
  exact (A.toSection.contMDiff.comp_contMDiffOn contMDiffOn_fst).mono
    (Set.subset_univ _)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem joint_app
    (g : SmoothRiemannianMetric I M) {a b c : ℕ} {S : Set ℝ}
    (A : ℝ → SmoothCcTensor g b c) (B : ℝ → SmoothCcTensor g a b)
    (hA : JointRS (I := I) g b c S A)
    (hB : JointRS (I := I) g a b S B) :
    JointRS (I := I) g a c S
      (fun t => ccOperatorFieldComp (I := I) (M := M) g a b c (A t) (B t)) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel a ℝ E) (V₁ := fun x : M => Tensor0SSpace a I x)
    (F₂ := Tensor0SModel c ℝ E) (V₂ := fun x : M => Tensor0SSpace c I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SSpace a I p.1 →L[ℝ] Tensor0SSpace c I p.1 from
        (ccOperatorFieldComp (I := I) (M := M) g a b c
          (A p.2) (B p.2)).toSection p.1))
    (S := S)
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel a ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel a ℝ E)
        (E := fun x : M => Tensor0SSpace a I x) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ S) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hBY := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hB hY
  have hABY := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hA hBY
  refine hABY.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel c ℝ E)
    (E := fun x : M => Tensor0SSpace c I x) p.1 z) ?_
  rw [operatorFieldComposition_toSection]
  rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem path_app_zero
    (g : SmoothRiemannianMetric I M) {b c : ℕ}
    (A : ℝ → SmoothCcTensor g b c) (W : SmoothCcTensor g 0 b)
    (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hA : JointRS (I := I) g b c S A)
    (hApp : JointRS (I := I) g 0 c S
      (fun t => ccOperatorFieldComp (I := I) (M := M) g 0 b c (A t) W)) :
    pathIntegralCoeffField (I := I) (M := M) g 0 c
        (fun t => ccOperatorFieldComp (I := I) (M := M) g 0 b c (A t) W)
        S hS hSI hApp =
      operatorFieldApply (I := I) (M := M) g b c
        (pathIntegralCoeffField (I := I) (M := M) g b c
          A S hS hSI hA) W := by
  classical
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  have hcontA : ∀ y : M, ContinuousOn
      (fun t : ℝ => TensorRSSpace.toModel ((A t).toSection y)) S :=
    fun y => jointContMDiff_toModel_continuous_slice
      (I := I) g b c A S hA y
  rw [pathIntegralCoeffField_operatorFieldApplication_eq
    (I := I) (M := M) g b c A W S hS hSI hA hcontA x v]
  let Ψ : ℝ → SmoothCcTensor g 0 c :=
    fun t => ccOperatorFieldComp (I := I) (M := M) g 0 b c (A t) W
  let u : Tensor0SModel 0 ℝ E :=
    Tensor0SSpace.toModel
      (unitTensor (I := I) (M := M) x)
  have hcontΨ : ContinuousOn
      (fun t : ℝ => TensorRSSpace.toModel ((Ψ t).toSection x)) S :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 0 c Ψ S hApp x
  have hΨInt : IntervalIntegrable
      (fun t : ℝ => TensorRSSpace.toModel ((Ψ t).toSection x))
      volume 0 1 :=
    (hcontΨ.mono hSI).intervalIntegrable
  have hcontApp : ContinuousOn
      (fun t : ℝ =>
        (TensorRSSpace.toModel ((Ψ t).toSection x)) u) S :=
    (ContinuousLinearMap.apply ℝ (Tensor0SModel c ℝ E) u).continuous.comp_continuousOn
      hcontΨ
  have hΨAppInt : IntervalIntegrable
      (fun t : ℝ =>
        (TensorRSSpace.toModel ((Ψ t).toSection x)) u)
      volume 0 1 :=
    (hcontApp.mono hSI).intervalIntegrable
  let L : Tensor0SModel c ℝ E →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin c => E) ℝ v
  simp only [unitModel]
  rw [toModel_tensorRS_apply (I := I) 0 c x]
  rw [pathIntegralCoeffField_toModel]
  rw [ContinuousLinearMap.intervalIntegral_apply hΨInt u]
  change L (∫ t in (0 : ℝ)..1,
    (TensorRSSpace.toModel ((Ψ t).toSection x)) u) =
      ∫ t in (0 : ℝ)..1,
        unitModel (I := I) (M := M) g c
          (operatorFieldApply (I := I) (M := M) g b c (A t) W) x v
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm L hΨAppInt]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  change unitModel (I := I) (M := M) g c (Ψ t) x v =
    unitModel (I := I) (M := M) g c
      (operatorFieldApply (I := I) (M := M) g b c (A t) W) x v
  simp only [Ψ, operatorFieldComposition_zero_eq_operatorFieldApply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem joint_param_smul
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {S : Set ℝ}
    (A : ℝ → SmoothCcTensor g r s)
    (hA : JointRS (I := I) g r s S A) :
    JointRS (I := I) g r s S (fun t => t • A t) := by
  let _ := tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) r s
  intro p hp
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x := p.1 with hx
  set e := trivializationAt (TensorRSModel r s ℝ E)
    (fun z : M => TensorRSSpace r s I z) x with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace
    (F := TensorRSModel r s ℝ E)
    (E := fun z : M => TensorRSSpace r s I z)).mp (hA p hp)
  refine (contMDiffWithinAt_snd.smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ q : M × ℝ in
        nhdsWithin p ((Set.univ : Set M) ×ˢ S), q.1 ∈ e.baseSet :=
      (continuousWithinAt_fst
        (s := (Set.univ : Set M) ×ˢ S) (p := p))
        (e.open_baseSet.mem_nhds (by
          rw [he]
          exact mem_baseSet_trivializationAt _ _ x))
    filter_upwards [hbase] with q hq
    exact (e.linear ℝ hq).map_smul q.2 ((A q.2).toSection q.1)
  · exact (e.linear ℝ (by
      rw [he, ← hx]
      exact mem_baseSet_trivializationAt _ _ x)).map_smul
        p.2 ((A p.2).toSection p.1)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
open DifferentialGeometry.Integral.DivergenceTheorem in
private theorem joint_curry {d : ℕ} {S : Set ℝ}
    (A : ∀ p : M × ℝ, Tensor0SSpace (d + 1) I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (d + 1) I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SModel d ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace d I z) p.1
        (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) d p.1 (A p)))
      ((Set.univ : Set M) ×ˢ S) := by
  let _ := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) (d + 1)
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hA' := (Bundle.contMDiffWithinAt_totalSpace
    (F := Tensor0SModel (d + 1) ℝ E)
    (E := fun z : M => Tensor0SSpace (d + 1) I z)).mp (hA p₀ hp₀)
  have hcurry : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, E →L[ℝ] Tensor0SModel d ℝ E) ∞
      (fun p : M × ℝ =>
        continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (d + 1) => E) ℝ
          ((trivializationAt (Tensor0SModel (d + 1) ℝ E)
            (fun z : M => Tensor0SSpace (d + 1) I z) x₀
            ⟨p.1, A p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hop : ContMDiff 𝓘(ℝ, Tensor0SModel (d + 1) ℝ E)
        𝓘(ℝ, E →L[ℝ] Tensor0SModel d ℝ E) ∞
        (fun U : Tensor0SModel (d + 1) ℝ E =>
          continuousMultilinearCurryLeftEquiv ℝ
            (fun _ : Fin (d + 1) => E) ℝ U) :=
      ((continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (d + 1) => E) ℝ
        ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
    exact hop.contMDiffAt.comp_contMDiffWithinAt p₀ hA'.2
  refine hcurry.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in
        nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (trivializationAt (Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SSpace d I z) x₀).baseSet :=
      (continuousWithinAt_fst
        (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((trivializationAt (Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SSpace d I z) x₀).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    have hc :=
      TensorMultilinear.trivializationAt_homBundle_curriedSection_eq
        (I := I) (M := M) (fun z : M => A ⟨z, p.2⟩) x₀ p.1 hx
    rw [TensorMultilinear.curriedSection] at hc
    exact hc
  · have hx0 : p₀.1 ∈
        (trivializationAt (Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SSpace d I z) x₀).baseSet := by
      rw [← hx₀]
      exact mem_baseSet_trivializationAt _ _ x₀
    have hc :=
      TensorMultilinear.trivializationAt_homBundle_curriedSection_eq
        (I := I) (M := M) (fun z : M => A ⟨z, p₀.2⟩) x₀ p₀.1 hx0
    rw [TensorMultilinear.curriedSection] at hc
    exact hc

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
open DifferentialGeometry.Integral.DivergenceTheorem in
private theorem joint_uncurry {d : ℕ} {S : Set ℝ}
    (G : ∀ p : M × ℝ,
      TangentSpace I p.1 →L[ℝ] Tensor0SSpace d I p.1)
    (hG : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SModel d ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace d I z)
        p.1 (G p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (d + 1) I z) p.1
        ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) d p.1).symm
          (G p)))
      ((Set.univ : Set M) ×ˢ S) := by
  let _ := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) (d + 1)
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hG' := (Bundle.contMDiffWithinAt_totalSpace
    (F := E →L[ℝ] Tensor0SModel d ℝ E)
    (E := fun z : M =>
      TangentSpace I z →L[ℝ] Tensor0SSpace d I z)).mp (hG p₀ hp₀)
  have huncurry : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SModel (d + 1) ℝ E) ∞
      (fun p : M × ℝ =>
        (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (d + 1) => E) ℝ).symm
          ((trivializationAt (E →L[ℝ] Tensor0SModel d ℝ E)
            (fun z : M =>
              TangentSpace I z →L[ℝ] Tensor0SSpace d I z) x₀
            ⟨p.1, G p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hop : ContMDiff 𝓘(ℝ, E →L[ℝ] Tensor0SModel d ℝ E)
        𝓘(ℝ, Tensor0SModel (d + 1) ℝ E) ∞
        (fun U : E →L[ℝ] Tensor0SModel d ℝ E =>
          (continuousMultilinearCurryLeftEquiv ℝ
            (fun _ : Fin (d + 1) => E) ℝ).symm U) :=
      ((continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (d + 1) => E) ℝ
        ).toContinuousLinearEquiv.symm.toContinuousLinearMap).contMDiff
    exact hop.contMDiffAt.comp_contMDiffWithinAt p₀ hG'.2
  have hpt : ∀ p : M × ℝ,
      p.1 ∈ (trivializationAt (Tensor0SModel d ℝ E)
          (fun y : M => Tensor0SSpace d I y) x₀).baseSet →
      (trivializationAt (Tensor0SModel (d + 1) ℝ E)
          (fun y : M => Tensor0SSpace (d + 1) I y) x₀
          ⟨p.1, (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ)
            d p.1).symm (G p)⟩).2 =
        (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (d + 1) => E) ℝ).symm
          ((trivializationAt (E →L[ℝ] Tensor0SModel d ℝ E)
            (fun y : M =>
              TangentSpace I y →L[ℝ] Tensor0SSpace d I y) x₀
            ⟨p.1, G p⟩).2) := by
    intro p hz
    have hUcurry :
        TensorMultilinear.curriedSection (I := I) (M := M)
          (fun y : M =>
            (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ)
              d y).symm (G ⟨y, p.2⟩)) p.1 = G p := by
      rw [TensorMultilinear.curriedSection]
      exact ContinuousLinearEquiv.apply_symm_apply _ _
    have hfwd :=
      TensorMultilinear.trivializationAt_homBundle_curriedSection_eq
        (I := I) (M := M)
        (fun y : M =>
          (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ)
            d y).symm (G ⟨y, p.2⟩)) x₀ p.1 hz
    rw [hUcurry] at hfwd
    rw [hfwd]
    exact (LinearIsometryEquiv.symm_apply_apply
      (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (d + 1) => E) ℝ) _).symm
  refine huncurry.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in
        nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (trivializationAt (Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SSpace d I z) x₀).baseSet :=
      (continuousWithinAt_fst
        (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((trivializationAt (Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SSpace d I z) x₀).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact hpt p hx
  · have hx0 : p₀.1 ∈
        (trivializationAt (Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SSpace d I z) x₀).baseSet := by
      rw [← hx₀]
      exact mem_baseSet_trivializationAt _ _ x₀
    apply hpt
    exact hx0

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem slotExtend_joint
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {S : Set ℝ}
    (A : ℝ → SmoothCcTensor g r s)
    (hA : JointRS (I := I) g r s S A) :
    JointRS (I := I) g (r + 1) (s + 1) S
      (fun t => slotExtend (I := I) (M := M) g r s (A t)) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel (r + 1) ℝ E)
    (V₁ := fun x : M => Tensor0SSpace (r + 1) I x)
    (F₂ := Tensor0SModel (s + 1) ℝ E)
    (V₂ := fun x : M => Tensor0SSpace (s + 1) I x)
    (φ := fun p : M × ℝ =>
      (slotExtend (I := I) (M := M) g r s (A p.2)).toSection p.1)
    (S := S)
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel (r + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk'
        (Tensor0SModel (r + 1) ℝ E)
        (E := fun x : M => Tensor0SSpace (r + 1) I x)
        p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ S) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hcur := joint_curry (I := I) (M := M) (d := r) (S := S)
    (fun p : M × ℝ => Y p.1) hY
  have hcomp : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk'
        (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] Tensor0SSpace s I x) p.1
        (((A p.2).toSection p.1).comp
          ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ)
            r p.1) (Y p.1))))
      ((Set.univ : Set M) ×ˢ S) := by
    apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := Tensor0SModel s ℝ E)
      (V₂ := fun x : M => Tensor0SSpace s I x)
      (φ := fun p : M × ℝ =>
        ((A p.2).toSection p.1).comp
          ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ)
            r p.1) (Y p.1)))
      (S := S)
    intro Z
    have hZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' E
          (E := fun x : M => TangentSpace I x) p.1 (Z p.1))
        ((Set.univ : Set M) ×ˢ S) :=
      Z.contMDiff.comp_contMDiffOn contMDiffOn_fst
    have hcurZ := ContMDiffOn.clm_bundle_apply
      (b := Prod.fst) hcur hZ
    have hAZ := ContMDiffOn.clm_bundle_apply
      (b := Prod.fst) hA hcurZ
    refine hAZ.congr (fun p _ => ?_)
    rfl
  have hout := joint_uncurry (I := I) (M := M)
    (d := s) (S := S)
    (fun p : M × ℝ =>
      (((A p.2).toSection p.1).comp
        ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ)
          r p.1) (Y p.1)))) hcomp
  refine hout.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk'
    (Tensor0SModel (s + 1) ℝ E)
    (E := fun x : M => Tensor0SSpace (s + 1) I x) p.1 z) ?_
  rw [slotExtend_toSection,
    DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply]

private def smoothCcTensorOfCovariantSection
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (Y : Cₛ^∞⟮I; Tensor0SModel s ℝ E,
      (fun x : M => Tensor0SSpace s I x)⟯) :
    SmoothCcTensor g 0 s where
  toSection :=
    MixedSection.fromMultilinearSection
      (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ Y
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem smoothCcTensorOfCovariantSection_apply_unitTensor
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (Y : Cₛ^∞⟮I; Tensor0SModel s ℝ E,
      (fun x : M => Tensor0SSpace s I x)⟯) (x : M) :
    (smoothCcTensorOfCovariantSection (I := I) (M := M) g Y).toSection x
        (unitZeroSec (I := I) (M := M) x) = Y x := by
  change
    (MixedSection.fromMultilinearSection
      (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ Y) x
        (unitZeroSec (I := I) (M := M) x) = Y x
  change (MixedSection.eval₀ (F := E)
      (E := (TangentSpace I : M → Type _)) x).smulRight (Y x)
        (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x
          (unitZeroSec (I := I) (M := M) x)) = Y x
  have hunit :
      tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x
          (unitZeroSec (I := I) (M := M) x) =
        ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) 1 := by
    rw [unitZeroSec_apply]
    apply ContinuousMultilinearMap.ext
    intro v
    change (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x
        ((tensor0SSpaceContinuousLinearEquiv (I := I) 0 x).symm
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) 1))) v = _
    rw [tensor0SSpaceFiberContinuousLinearEquiv_model_symm_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply]
  change MixedSection.eval₀ (F := E)
      (E := (TangentSpace I : M → Type _)) x
        (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x
          (unitZeroSec (I := I) (M := M) x)) • Y x = Y x
  rw [hunit, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem joint_eval0
    (g : SmoothRiemannianMetric I M) {s : ℕ} {S : Set ℝ}
    (A : ℝ → SmoothCcTensor g 0 s)
    (hA : JointRS (I := I) g 0 s S A) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun x : M => Tensor0SSpace s I x) p.1
        ((A p.2).toSection p.1
          (unitZeroSec (I := I) (M := M) p.1)))
      ((Set.univ : Set M) ×ˢ S) := by
  have hu : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun x : M => Tensor0SSpace 0 I x) p.1
        (unitZeroSec (I := I) (M := M) p.1))
      ((Set.univ : Set M) ×ˢ S) :=
    (unitZeroSec (I := I) (M := M)).contMDiff.comp_contMDiffOn
      contMDiffOn_fst
  exact ContMDiffOn.clm_bundle_apply (b := Prod.fst) hA hu

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem arm_const
    (g : SmoothRiemannianMetric I M) {r : ℕ}
    (A : SmoothCcTensor g r 2) {δ δ' : ℝ} :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g r
      (fun _ => A) (δ := δ) (δ' := δ') := by
  exact joint_const (I := I) (M := M)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ')) g A

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem arm_comp
    (g : SmoothRiemannianMetric I M) (a b : ℕ)
    (A : ℝ → SmoothCcTensor g b 2) (B : SmoothCcTensor g a b)
    {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g b A
      (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g a
      (fun t => ccOperatorFieldComp (I := I) (M := M) g a b 2 (A t) B)
      (δ := δ) (δ' := δ') := by
  have hA' : JointRS (I := I) g b 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) A := hA
  have hB := joint_const (I := I) (M := M)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ')) g B
  exact joint_app (I := I) (M := M)
    (a := a) (b := b) (c := 2) g A (fun _ => B) hA' hB

omit [CompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem fullRaised_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) p.1
        (metricComparisonEndomorphismField (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ p.2) p.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ)) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun p : M × ℝ =>
      metricComparisonEndomorphismField (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ p.2) p.1)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ))
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E
        (E := fun x : M => TangentSpace I x) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ)) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hflat : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel 1 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SModel 1 ℝ E)
        (E := fun x : M => TangentSpace I x →L[ℝ] Tensor0SSpace 1 I x) p.1
        (g0FlatCLM (I := I) g p.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ)) :=
    (g0FlatField_contMDiff (I := I) g).comp_contMDiffOn contMDiffOn_fst
  have hflatY := ContMDiffOn.clm_bundle_apply
    (b := Prod.fst) hflat hY
  have hsharp :=
    inverseMetricSharpField_metricPerturbationPath_jointContMDiffOn
      (I := I) (M := M) g T 0 hδ hδZ
  have hout := ContMDiffOn.clm_bundle_apply
    (b := Prod.fst) hsharp hflatY
  refine hout.congr (fun p _ => ?_)
  rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem slotInsert_joint
    (g : SmoothRiemannianMetric I M) (d : ℕ)
    (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointRS (I := I) g (d + 1) (d + 1)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => slotInsertEndoCc (I := I) (M := M) g d
        (metricComparisonEndomorphismField (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ t))) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel (d + 1) ℝ E)
    (V₁ := fun x : M => Tensor0SSpace (d + 1) I x)
    (F₂ := Tensor0SModel (d + 1) ℝ E)
    (V₂ := fun x : M => Tensor0SSpace (d + 1) I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SSpace (d + 1) I p.1 →L[ℝ]
          Tensor0SSpace (d + 1) I p.1 from
        (slotInsertEndoCc (I := I) (M := M) g d
          (metricComparisonEndomorphismField (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδ hδZ p.2))).toSection p.1))
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ))
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel (d + 1) ℝ E)
        (E := fun x : M => Tensor0SSpace (d + 1) I x) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ)) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hout := slotInsertEndo0Field_apply_jointContMDiffOn
    (I := I) (M := M) (d := d)
    (fun p : M × ℝ => metricComparisonEndomorphismField (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hδ hδZ p.2) p.1)
    (fullRaised_joint (I := I) (M := M) g T hδ hδZ)
    (fun p : M × ℝ => Y p.1) hY
  refine hout.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel (d + 1) ℝ E)
    (E := fun x : M => Tensor0SSpace (d + 1) I x) p.1 z) ?_
  rw [slotInsertEndoCc_toSection]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem connectionDifferenceLowOrderOperator_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointRS (I := I) g 3 3
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => connectionDifferenceLowOrderOperator (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)) := by
  have hi := slotInsert_joint (I := I) (M := M) g 2 T hδ hδZ
  have hk := joint_const (I := I) (M := M) (S :=
    metricPerturbationPathDomain (δ := δ) (δ' := δ))
    g (koszulOp (I := I) (M := M) g)
  have hinner := joint_app (I := I) (M := M) g _ _ hi hk
  have hp := joint_const (I := I) (M := M) (S :=
    metricPerturbationPathDomain (δ := δ) (δ' := δ))
    g (permCoeff (I := I) (M := M) g connectionDifferenceLowOrderPermutation)
  have hout := joint_app (I := I) (M := M) g _ _ hp hinner
  simpa only [connectionDifferenceLowOrderOperator] using hout

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem dagTop_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointRS (I := I) g 4 4
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => ricciConnectionPrincipalCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)) := by
  have hc := connectionDifferenceLowOrderOperator_joint (I := I) (M := M) g T hδ hδZ
  have hs := slotExtend_joint (I := I) (M := M) g _ hc
  have hp := joint_const (I := I) (M := M) (S :=
    metricPerturbationPathDomain (δ := δ) (δ' := δ))
    g (permCoeff (I := I) (M := M) g ricciConnectionDifferenceDerivativeCyclicPermutation)
  have hout := joint_app (I := I) (M := M) g _ _ hp hs
  simpa only [ricciConnectionPrincipalCoefficient] using hout

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem daMono_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (G : SmoothCcTensor g 0 4) (σ : Equiv.Perm (Fin 4)) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) G σ)
      (δ := δ) (δ' := δ) := by
  have hk := joint_const (I := I) (M := M) (S :=
    metricPerturbationPathDomain (δ := δ) (δ' := δ))
    g (decompositionKernelContractionMonomialField
      (I := I) (M := M) g g G σ)
  have hi := slotInsert_joint (I := I) (M := M) g 1 T hδ hδZ
  have hout := joint_app (I := I) (M := M) g _ _ hk hi
  simpa only [linearizedRicciThreeArmHjoint, ricciConnectionDifferenceDerivativeContractionMonomial] using hout

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem daContr_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (G : SmoothCcTensor g 0 4) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => ricciConnectionDifferenceDerivativeContraction (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) G)
      (δ := δ) (δ' := δ) := by
  have hA := daMono_joint (I := I) (M := M)
    g T hδ hδZ G ricciConnectionDifferenceDerivativeCyclicPermutation
  have hB := daMono_joint (I := I) (M := M)
    g T hδ hδZ G ricciConnectionDifferenceDerivativeFirstPairSwap
  simpa only [ricciConnectionDifferenceDerivativeContraction] using
    threeArmJoint_sub (I := I) (M := M) g _ _ hA hB

omit [BoundarylessManifold I M] in
omit sigmaCompactSpace in
private theorem daTrans_joint
    (g : SmoothRiemannianMetric I M) (T W : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 4
      (fun t => ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) W)
      (δ := δ) (δ' := δ) := by
  rw [linearizedRicciThreeArmHjoint]
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 4 ℝ E)
    (V₁ := fun x : M => Tensor0SSpace 4 I x)
    (F₂ := Tensor0SModel 2 ℝ E)
    (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      (ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ p.2) W).toSection p.1)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ))
  intro G
  let Gc : SmoothCcTensor g 0 4 :=
    smoothCcTensorOfCovariantSection (I := I) (M := M) g G
  have hc := daContr_joint (I := I) (M := M)
    g T hδ hδZ Gc
  have hc' : JointRS (I := I) g 2 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => ricciConnectionDifferenceDerivativeContraction (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) Gc) := hc
  have hW := joint_const (I := I) (M := M) (S :=
    metricPerturbationPathDomain (δ := δ) (δ' := δ)) g W
  have hout := joint_app (I := I) (M := M)
    (a := 0) (b := 2) (c := 2) g _ _ hc' hW
  have heval := joint_eval0 (I := I) (M := M) g _ hout
  refine heval.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun x : M => Tensor0SSpace 2 I x) p.1 z) ?_
  have h := congrArg (fun Z : SmoothCcTensor g 0 2 => Z.toSection p.1)
    (daContr_trans (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hδ hδZ p.2)
      Gc W)
  have hunit := congrArg
    (fun L : Tensor0SSpace 0 I p.1 →L[ℝ] Tensor0SSpace 2 I p.1 =>
      L (unitZeroSec (I := I) (M := M) p.1)) h
  simp only [operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply] at hunit
  rw [show Gc.toSection p.1
      (unitZeroSec (I := I) (M := M) p.1) = G p.1 by
    exact smoothCcTensorOfCovariantSection_apply_unitTensor (I := I) (M := M) g G p.1] at hunit
  simpa only [operatorFieldComposition_zero_eq_operatorFieldApply, operatorFieldApplication_toSection,
    ContinuousLinearMap.comp_apply] using hunit.symm

omit [BoundarylessManifold I M] in
omit sigmaCompactSpace in
private theorem ricciTop_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 4
      (fun t => ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) T)
      (δ := δ) (δ' := δ) := by
  have hA := daTrans_joint (I := I) (M := M)
    g T T hδ hδZ
  have hB := dagTop_joint (I := I) (M := M)
    g T hδ hδZ
  have hA' : JointRS (I := I) g 4 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) T) := hA
  rw [linearizedRicciThreeArmHjoint]
  have hout := joint_app (I := I) (M := M)
    (a := 4) (b := 4) (c := 2) g _ _ hA' hB
  simpa only [ricciConnectionDifferenceTopOrderCoefficient, ricciCovariantDerivativeConnectionDifferenceTopOrder] using hout

omit sigmaCompactSpace in
omit [BoundarylessManifold I M] in
private theorem danger_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => ricciConnectionDifferenceSecondDerivativeContraction (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) (t • T))
      (δ := δ) (δ' := δ) := by
  rw [linearizedRicciThreeArmHjoint]
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E)
    (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E)
    (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      (ricciConnectionDifferenceSecondDerivativeContraction (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ p.2)
        (p.2 • T)).toSection p.1)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ))
  intro W
  let Wc : SmoothCcTensor g 0 2 :=
    smoothCcTensorOfCovariantSection (I := I) (M := M) g W
  have hTop := daTrans_joint (I := I) (M := M)
    g T Wc hδ hδZ
  have hTop' : JointRS (I := I) g 4 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) Wc) := hTop
  have hDag := dagTop_joint (I := I) (M := M)
    g T hδ hδZ
  have hD2 := joint_const (I := I) (M := M) (S :=
    metricPerturbationPathDomain (δ := δ) (δ' := δ)) g
    (iteratedCovGrad (I := I) g 0 2 2 T)
  have hsD2 := joint_param_smul (I := I) (M := M) g _ hD2
  have hG := joint_app (I := I) (M := M) g _ _ hDag hsD2
  have hout := joint_app (I := I) (M := M)
    (a := 0) (b := 4) (c := 2) g _ _ hTop' hG
  have heval := joint_eval0 (I := I) (M := M) g _ hout
  refine heval.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun x : M => Tensor0SSpace 2 I x) p.1 z) ?_
  have h := congrArg (fun Z : SmoothCcTensor g 0 2 => Z.toSection p.1)
    (daContr_trans (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hδ hδZ p.2)
      (ccOperatorFieldComp (I := I) (M := M) g 0 4 4
        (ricciConnectionPrincipalCoefficient (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ p.2))
        (iteratedCovGrad (I := I) g 0 2 2 (p.2 • T)))
      Wc)
  have hunit := congrArg
    (fun L : Tensor0SSpace 0 I p.1 →L[ℝ] Tensor0SSpace 2 I p.1 =>
      L (unitZeroSec (I := I) (M := M) p.1)) h
  simp only [operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply] at hunit
  rw [show Wc.toSection p.1
      (unitZeroSec (I := I) (M := M) p.1) = W p.1 by
    exact smoothCcTensorOfCovariantSection_apply_unitTensor (I := I) (M := M) g W p.1] at hunit
  simpa only [ricciConnectionDifferenceSecondDerivativeContraction, iteratedCovGrad_smul,
    operatorFieldComposition_zero_eq_operatorFieldApply, operatorFieldApplication_toSection,
    ContinuousLinearMap.comp_apply] using hunit

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem inputSymm_joint
    (g : SmoothRiemannianMetric I M) {δ : ℝ}
    (C : ℝ → SmoothCcTensor g 2 2)
    (hC : linearizedRicciThreeArmHjoint (I := I) (M := M) g 2 C
      (δ := δ) (δ' := δ)) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => ccInputSlotSymm (I := I) (M := M) g (C t))
      (δ := δ) (δ' := δ) := by
  have hswap := joint_app (I := I) (M := M) g C
    (fun _ => ccSlotSwapField (I := I) (M := M) g) hC
    (joint_const (I := I) (M := M) (S :=
      metricPerturbationPathDomain (δ := δ) (δ' := δ)) g
      (ccSlotSwapField (I := I) (M := M) g))
  change linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
    (fun t => ccOperatorFieldComp (I := I) (M := M) g 2 2 2
      (C t) (ccSlotSwapField (I := I) (M := M) g))
      (δ := δ) (δ' := δ) at hswap
  have hadd := threeArmJoint_add (I := I) (M := M) g _ _ hC hswap
  simpa only [ccInputSlotSymm] using
    threeArmJoint_smul (I := I) (M := M) g (1 / 2 : ℝ) _ hadd

omit sigmaCompactSpace in
private theorem safeLow_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => reducedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) (t • T))
      (δ := δ) (δ' := δ) := by
  have hraw :=
    linearizedRicciConnectionDifferenceOrder0Coeff_jointContMDiffOn_smallPerturbationSet
      (I := I) (M := M) g T 0 hδ hδZ
  have hdanger := danger_joint (I := I) (M := M)
    g T hδ hδZ
  have hsub := threeArmJoint_sub (I := I) (M := M)
    g _ _ hraw hdanger
  have hsymm := inputSymm_joint (I := I) (M := M) g _ hsub
  change linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => ccInputSlotSymm (I := I) (M := M) g
        (linearizedRicciConnectionDifferenceOrder0CoeffField
            (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδ hδZ t) -
          ricciConnectionDifferenceSecondDerivativeContraction
            (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδ hδZ t) (t • T)))
      (δ := δ) (δ' := δ) at hsymm
  exact hsymm

omit sigmaCompactSpace in
private theorem half_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => ricciPalatiniHalfCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t))
      (δ := δ) (δ' := δ) := by
  have hconn :=
    linearizedRicciConnectionDifferenceOrder0Coeff_jointContMDiffOn_smallPerturbationSet
      (I := I) (M := M) g T 0 hδ hδZ
  have hriem : linearizedRicciThreeArmHjoint
      (I := I) (M := M) g 2
      (fun t => ricciArmOrder0RiemannCoeff
        (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t))
      (δ := δ) (δ' := δ) := by
    rw [linearizedRicciThreeArmHjoint]
    exact ricciArmOrder0RiemannCoeff_metricPerturbationPath_jointContMDiff
      (I := I) (M := M) g T 0 hδ hδZ
  have hsum := threeArmJoint_add (I := I) (M := M) g _ _
    hconn (threeArmJoint_smul (I := I) (M := M)
      g (1 / 2 : ℝ) _ hriem)
  simpa only [ricciPalatiniHalfCoefficient,
    linearizedRicciConnectionDifferenceOrder0Coeff] using hsum

omit sigmaCompactSpace in
private theorem low_order_decomposition_joint_continuous
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => ricciDecomposition0 (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) (t • T))
      (δ := δ) (δ' := δ) := by
  have hriem := arm_const (I := I) (M := M) g
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g g)
    (δ := δ) (δ' := δ)
  have hAA :=
    ricciArmOrder0AACommCoeffField_metricPerturbationPath_threeArmHjoint
      (I := I) (M := M) g T hδ hδZ
  have hBackground :=
    ricciArmOrder0BackgroundRCommCoeffField_metricPerturbationPath_threeArmHjoint
      (I := I) (M := M) g T hδ hδZ
  have hBackground0 := arm_const (I := I) (M := M) g
    (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g g)
    (δ := δ) (δ' := δ)
  have hBackgroundDiff := threeArmJoint_sub (I := I) (M := M)
    g _ _ hBackground hBackground0
  have hSwap := arm_comp (I := I) (M := M) g 2 2 _
    (ccSlotSwapField (I := I) (M := M) g) hBackgroundDiff
  have hSharp :=
    ricciArmSharpGradKoszulResidualField_metricPerturbationPath_threeArmHjoint
      (I := I) (M := M) g T hδ hδZ
  have hFold :=
    ricciArmRicciFoldRemainderField_metricPerturbationPath_threeArmHjoint
      (I := I) (M := M) g T hδ hδZ
  have htail := threeArmJoint_sub (I := I) (M := M) g _ _
    (threeArmJoint_add (I := I) (M := M) g _ _ hSwap
      (threeArmJoint_smul (I := I) (M := M)
        g (1 / 2 : ℝ) _ hSharp))
    hFold
  have hinner := threeArmJoint_add (I := I) (M := M)
    g _ _ hAA htail
  have hall := threeArmJoint_add (I := I) (M := M) g _ _ hriem
    (threeArmJoint_smul (I := I) (M := M) g (2 : ℝ) _ hinner)
  simpa only [ricciDecomposition0] using hall

private def pathIntegrand
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 2 2 :=
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  (-2 : ℝ) • reducedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm (s • T) +
    deTurckLieCoeffField (I := I) (M := M) g gm g_bg +
    lieCorrectionZeroField (I := I) (M := M) g gm g_bg -
    deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
      lieDecompositionQ lieDecompositionEps s

omit sigmaCompactSpace in
private theorem rhsSelf_good
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    pathIntegrand (I := I) (M := M) g g_bg T hδ hδZ s =
      let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
      (-2 : ℝ) • symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm (s • T) +
        deTurckLieCoeffField (I := I) (M := M) g gm g_bg +
        lieCorrectionZeroField (I := I) (M := M) g gm g_bg -
        deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
          lieDecompositionQ lieDecompositionEps s := by
  let P : SmoothCcTensor g 0 2 := s • T
  let gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδ hδZ s
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    rw [← show convexPerturbation (I := I) g T 0 s = P by
      simp only [P, convexPerturbation, smul_zero, zero_add]]
    exact metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hδ hδZ hs_mem x u v
  have hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [P, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hgood := ricciGood_eq_safe (I := I) (M := M) g gm P hP htie
  simp only [pathIntegrand]
  rw [← hgood]

private def ricciDeTurckSelfTopOrderCoefficient
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 4 2 :=
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  (-2 * s : ℝ) • ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T +
    (-1 : ℝ) • ricciDecomposition2 (I := I) (M := M) g T hδ hδZ s

omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem topKernel_eq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
    rhsDecompositionTop (I := I) (M := M) g T hδ hδZ s +
          ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ s -
          deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g =
      lieDecomposition2 (I := I) (M := M) g T hδ hδZ s +
        (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gm -
          deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g) +
        (-2 * s : ℝ) • ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T := by
  simp only [rhsDecompositionTop, rhsDecomposition2, ricciDeTurckSelfTopOrderCoefficient]
  module

omit sigmaCompactSpace in
omit [I.Boundaryless] in
private theorem lieLow_decomp
    (g gm g_bg : SmoothRiemannianMetric I M)
    (Q : SmoothCcTensor g 2 2) :
    deTurckLieCoeffField (I := I) (M := M) g gm g_bg +
          lieCorrectionZeroField (I := I) (M := M) g gm g_bg - Q =
      (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g gm g_bg - Q) +
        (deTurckLieEndoArmField (I := I) (M := M) g gm g_bg -
          deTurckLieEndoArmField (I := I) (M := M) g gm g) +
        ((((lieCorrectionZeroInsertion (I := I) (M := M) g gm g_bg -
              lieCorrectionZeroInsertion (I := I) (M := M) g gm g) +
            lieCorrectionZeroVectorBundle (I := I) (M := M) g gm) +
          lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g_bg) +
        lieCorrectionZeroRiemann (I := I) (M := M) g gm) := by
  rw [deTurckLieCoeffField_eq_covDerivArm_add_endoArm]
  rw [← tail_base_split (I := I) (M := M) g gm g_bg]
  abel

omit sigmaCompactSpace in
private theorem selfLow_decomp
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    pathIntegrand (I := I) (M := M) g g_bg T hδ hδZ s =
      let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
      (-2 : ℝ) • reducedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm (s • T) +
        ((deTurckLieCovariantDerivativeArmField (I := I) (M := M) g gm g_bg -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
              lieDecompositionQ lieDecompositionEps s) +
          (deTurckLieEndoArmField (I := I) (M := M) g gm g_bg -
            deTurckLieEndoArmField (I := I) (M := M) g gm g) +
          ((((lieCorrectionZeroInsertion (I := I) (M := M) g gm g_bg -
                lieCorrectionZeroInsertion (I := I) (M := M) g gm g) +
              lieCorrectionZeroVectorBundle (I := I) (M := M) g gm) +
            lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g_bg) +
          lieCorrectionZeroRiemann (I := I) (M := M) g gm)) := by
  simp only [pathIntegrand]
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  let Q := deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
    lieDecompositionQ lieDecompositionEps s
  have hlie := lieLow_decomp (I := I) (M := M) g gm g_bg Q
  have hreassoc (A B C D : SmoothCcTensor g 2 2) :
      A + B + C - D = A + (B + C - D) := by
    module
  rw [hreassoc
    ((-2 : ℝ) • reducedRicciConnectionDifferenceLowOrderCoefficient
      (I := I) (M := M) g gm (s • T))
    (deTurckLieCoeffField (I := I) (M := M) g gm g_bg)
    (lieCorrectionZeroField (I := I) (M := M) g gm g_bg) Q, hlie]

private def oldRicci
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 2 2 :=
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  (-2 : ℝ) • ricciPalatiniHalfCoefficient (I := I) (M := M) g gm +
    ricciDecomposition0 (I := I) (M := M) g gm (s • T)

omit [SigmaCompactSpace M] in
private theorem selfLow_eq
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    pathIntegrand (I := I) (M := M) g g_bg T hδ hδZ s =
      (-2 : ℝ) • reducedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) (s • T) +
        (rhsDecomposition0 (I := I) (M := M) g g_bg T hδ hδZ s -
          oldRicci (I := I) (M := M) g T hδ hδZ s) := by
  simp only [pathIntegrand, oldRicci, rhsDecomposition0, lieDecomposition0]
  rw [deTurckLieCoeffField_eq_covDerivArm_add_endoArm]
  module

omit sigmaCompactSpace in
private theorem oldRicci_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (oldRicci (I := I) (M := M) g T hδ hδZ)
      (δ := δ) (δ' := δ) := by
  have hh := half_joint (I := I) (M := M) g T hδ hδZ
  have hscaled := threeArmJoint_smul (I := I) (M := M)
    g (-2 : ℝ) _ hh
  have hdecomposition := low_order_decomposition_joint_continuous (I := I) (M := M)
    g T hδ hδZ
  have hsum := threeArmJoint_add (I := I) (M := M)
    g _ _ hscaled hdecomposition
  change linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun s => (-2 : ℝ) • ricciPalatiniHalfCoefficient
          (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) +
        ricciDecomposition0 (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) (s • T))
      (δ := δ) (δ' := δ)
  exact hsum

omit sigmaCompactSpace in
private theorem selfLow_joint
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (pathIntegrand (I := I) (M := M) g g_bg T hδ hδZ)
      (δ := δ) (δ' := δ) := by
  have hsafe := safeLow_joint (I := I) (M := M)
    g T hδ hδZ
  have hsafe' := threeArmJoint_smul (I := I) (M := M)
    g (-2 : ℝ) _ hsafe
  have hfull := rhsDecomposition0_joint (I := I) (M := M)
    g g_bg T hδ hδZ
  have hold := oldRicci_joint (I := I) (M := M)
    g T hδ hδZ
  have htail := threeArmJoint_sub (I := I) (M := M)
    g _ _ hfull hold
  have hall := threeArmJoint_add (I := I) (M := M)
    g _ _ hsafe' htail
  convert hall using 1
  funext s
  exact selfLow_eq (I := I) (M := M)
    g g_bg T hδ hδZ s

omit [BoundarylessManifold I M] in
omit sigmaCompactSpace in
private theorem selfTop_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 4
      (ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ)
      (δ := δ) (δ' := δ) := by
  have htop := ricciTop_joint (I := I) (M := M)
    g T hδ hδZ
  have htop' : JointRS (I := I) g 4 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun s => ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ s) T) := htop
  have hparam := joint_param_smul (I := I) (M := M)
    g _ htop'
  change linearizedRicciThreeArmHjoint (I := I) (M := M) g 4
    (fun s => s • ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hδ hδZ s) T)
      (δ := δ) (δ' := δ) at hparam
  have htopScaled := threeArmJoint_smul (I := I) (M := M)
    g (-2 : ℝ) _ hparam
  have hpal :=
    riemannPalatiniDecompositionC2Family_threeArmHjoint
      (I := I) (M := M) g T hδ hδZ ricciDecompositionQA ricciDecompositionQB
  have hdecomposition := threeArmJoint_smul (I := I) (M := M)
    g (2 : ℝ) _ hpal
  have hdecomposition' : linearizedRicciThreeArmHjoint
      (I := I) (M := M) g 4
      (fun s => ricciDecomposition2 (I := I) (M := M)
        g T hδ hδZ s) (δ := δ) (δ' := δ) := by
    simpa only [ricciDecomposition2] using hdecomposition
  have hneg := threeArmJoint_smul (I := I) (M := M)
    g (-1 : ℝ) _ hdecomposition'
  have hall := threeArmJoint_add (I := I) (M := M)
    g _ _ htopScaled hneg
  change linearizedRicciThreeArmHjoint (I := I) (M := M) g 4
      (fun s => (-2 * s : ℝ) •
          ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδ hδZ s) T +
        (-1 : ℝ) • ricciDecomposition2 (I := I) (M := M) g T hδ hδZ s)
      (δ := δ) (δ' := δ)
  simpa only [smul_smul] using hall

omit sigmaCompactSpace in
private theorem rhs_self_decomposition
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (rhsDecomposition0 (I := I) (M := M) g g_bg T hδ hδZ s) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (pathIntegrand (I := I) (M := M) g g_bg T hδ hδZ s) T +
        operatorFieldApply (I := I) (M := M) g 4 2
          (ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ s)
          (iteratedCovGrad (I := I) g 0 2 2 T) := by
  let P : SmoothCcTensor g 0 2 := s • T
  let gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδ hδZ s
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    rw [← show convexPerturbation (I := I) g T 0 s = P by
      simp only [P, convexPerturbation, smul_zero, zero_add]]
    exact metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hδ hδZ hs_mem x u v
  have hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [P, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hconn := ricciConnectionDifference_decomposition (I := I) (M := M)
    g gm P T hP hT htie
  have hsafe := safeLow_action (I := I) (M := M)
    g gm P T hP hT htie
  have hkernel :=
    operatorFieldApplication_decompositionKernelContractionField (I := I) (M := M) g gm
      (iteratedCovGrad (I := I) g 0 2 2 P)
      (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 T
  have hsymm : symmS (I := I) (M := M) g T = T :=
    symm_eq_self (I := I) (M := M) g T hT
  have hpal :
      ricciDecomposition2 (I := I) (M := M) g T hδ hδZ s =
        (2 * s : ℝ) •
          curvatureDecompositionKernelCoeffField (I := I) (M := M) g gm
            (ccTensorUnitValueSection (I := I) (M := M) g T)
            (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g T)
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 *
              Equiv.swap (1 : Fin 4) 3) 1 := by
    rw [ricciDecomposition2,
      riemannC2_eq_kernel (I := I) (M := M) g T hδ hδZ
        ricciDecompositionQA ricciDecompositionQB (fun _ => rfl) s,
      hsymm, smul_smul]
    rfl
  rw [rhsDecomposition_eq (I := I) (M := M) g g_bg T
    hδ hδZ hT hδ_lt s hs]
  simp only [operatorFieldApplication_add_left, operatorFieldApplication_sub_left, operatorFieldApplication_smul_left]
  rw [hconn, ← hsafe, hkernel]
  simp only [P, iteratedCovGrad_smul, operatorFieldApplication_smul_right]
  have hLie :
      operatorFieldApply (I := I) (M := M) g 2 2
          (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gm g_bg) T +
        operatorFieldApply (I := I) (M := M) g 2 2
          (deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gm g_bg) T =
      operatorFieldApply (I := I) (M := M) g 2 2
        (deTurckLieCoeffField (I := I) (M := M) g gm g_bg) T := by
    rw [← operatorFieldApplication_add_left]
    rw [deTurckLieConnectionDifferenceDerivCoeffField_add_deTurckLieCovariantDerivativeInsertionField
      (I := I) (M := M) g gm g_bg]
  simp only [pathIntegrand, ricciDeTurckSelfTopOrderCoefficient, gm,
    operatorFieldApplication_add_left, operatorFieldApplication_sub_left,
    operatorFieldApplication_smul_left]
  rw [hpal]
  simp only [operatorFieldApplication_smul_left]
  rw [← sub_eq_zero]
  calc
    _ =
        (operatorFieldApply (I := I) (M := M) g 2 2
            (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gm g_bg) T +
          operatorFieldApply (I := I) (M := M) g 2 2
            (deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gm g_bg) T) -
        operatorFieldApply (I := I) (M := M) g 2 2
          (deTurckLieCoeffField (I := I) (M := M) g gm g_bg) T := by
      module
    _ = 0 := by rw [hLie, sub_self]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem unitModel_add
    (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 2) (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2 (A + B) x v =
      unitModel (I := I) (M := M) g 2 A x v +
        unitModel (I := I) (M := M) g 2 B x v := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
    Pi.add_apply, add_apply,
    Tensor0SSpace.toModel_add, add_apply]

private def selfLowInt
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 2 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 2 2
    (pathIntegrand (I := I) (M := M) g g_bg T hδ hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (selfLow_joint (I := I) (M := M) g g_bg T hδ hδZ)
private def selfTopInt
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 4 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 4 2
    (ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (selfTop_joint (I := I) (M := M) g T hδ hδZ)
omit sigmaCompactSpace in
private theorem zero_order_decomposition_self
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (rhsDecomposition0Int (I := I) (M := M) g g_bg T
          hδ_lt hδ hδZ) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (selfLowInt (I := I) (M := M) g g_bg T
            hδ_lt hδ hδZ) T +
        operatorFieldApply (I := I) (M := M) g 4 2
          (selfTopInt (I := I) (M := M) g T
            hδ_lt hδ hδZ)
          (iteratedCovGrad (I := I) g 0 2 2 T) := by
  classical
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  let Ψ : ℝ → SmoothCcTensor g 2 2 :=
    rhsDecomposition0 (I := I) (M := M) g g_bg T hδ hδZ
  let L : ℝ → SmoothCcTensor g 2 2 :=
    pathIntegrand (I := I) (M := M) g g_bg T hδ hδZ
  let Q : ℝ → SmoothCcTensor g 4 2 :=
    ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ
  have hjΨ : linearizedRicciThreeArmHjoint
      (I := I) (M := M) g 2 Ψ (δ := δ) (δ' := δ) :=
    rhsDecomposition0_joint (I := I) (M := M) g g_bg T hδ hδZ
  have hjL : linearizedRicciThreeArmHjoint
      (I := I) (M := M) g 2 L (δ := δ) (δ' := δ) :=
    selfLow_joint (I := I) (M := M) g g_bg T hδ hδZ
  have hjQ : linearizedRicciThreeArmHjoint
      (I := I) (M := M) g 4 Q (δ := δ) (δ' := δ) :=
    selfTop_joint (I := I) (M := M) g T hδ hδZ
  have hcΨ : ∀ x : M, ContinuousOn (fun t : ℝ =>
      TensorRSSpace.toModel ((Ψ t).toSection x))
      (metricPerturbationPathDomain (δ := δ) (δ' := δ)) := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2 Ψ
      (metricPerturbationPathDomain (δ := δ) (δ' := δ)) hjΨ x
  have hcL : ∀ x : M, ContinuousOn (fun t : ℝ =>
      TensorRSSpace.toModel ((L t).toSection x))
      (metricPerturbationPathDomain (δ := δ) (δ' := δ)) := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2 L
      (metricPerturbationPathDomain (δ := δ) (δ' := δ)) hjL x
  have hcQ : ∀ x : M, ContinuousOn (fun t : ℝ =>
      TensorRSSpace.toModel ((Q t).toSection x))
      (metricPerturbationPathDomain (δ := δ) (δ' := δ)) := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 4 2 Q
      (metricPerturbationPathDomain (δ := δ) (δ' := δ)) hjQ x
  have hPiΨ :
      rhsDecomposition0Int (I := I) (M := M) g g_bg T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2 Ψ
          (metricPerturbationPathDomain (δ := δ) (δ' := δ))
          metricPerturbationPathDomain_isOpen hSI hjΨ := rfl
  have hPiL :
      selfLowInt (I := I) (M := M) g g_bg T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2 L
          (metricPerturbationPathDomain (δ := δ) (δ' := δ))
          metricPerturbationPathDomain_isOpen hSI hjL := rfl
  have hPiQ :
      selfTopInt (I := I) (M := M) g T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 4 2 Q
          (metricPerturbationPathDomain (δ := δ) (δ' := δ))
          metricPerturbationPathDomain_isOpen hSI hjQ := rfl
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [hPiΨ, hPiL, hPiQ]
  rw [pathIntegralCoeffField_operatorFieldApplication_eq
      (I := I) (M := M) g 2 2 Ψ T
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      metricPerturbationPathDomain_isOpen hSI hjΨ hcΨ x v]
  rw [unitModel_add (I := I) (M := M) g]
  rw [pathIntegralCoeffField_operatorFieldApplication_eq
      (I := I) (M := M) g 2 2 L T
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      metricPerturbationPathDomain_isOpen hSI hjL hcL x v]
  rw [pathIntegralCoeffField_operatorFieldApplication_eq
      (I := I) (M := M) g 4 2 Q
      (iteratedCovGrad (I := I) g 0 2 2 T)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      metricPerturbationPathDomain_isOpen hSI hjQ hcQ x v]
  have hIL := coeffApp_integrable (I := I) (M := M)
    g 2 2 L T (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    hSI hcL x v
  have hIQ := coeffApp_integrable (I := I) (M := M)
    g 4 2 Q (iteratedCovGrad (I := I) g 0 2 2 T)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ)) hSI hcQ x v
  rw [← intervalIntegral.integral_add hIL hIQ]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le zero_le_one] at hs
  have hdecomposition := rhs_self_decomposition (I := I) (M := M)
    g g_bg T hT hδ_lt hδ hδZ hs
  have hmodel := congrArg
    (fun Z : SmoothCcTensor g 0 2 =>
      unitModel (I := I) (M := M) g 2 Z x v) hdecomposition
  simpa only [Ψ, L, Q, unitModel_add (I := I) (M := M) g] using hmodel
private theorem secondOrderCoefficient_fibre_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ}, δ ≤ 1 / 3 → 0 ≤ δ → ∀ (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            ((rhsDecompositionTopInt (I := I) (M := M) g T hδ_lt hδ hδZ +
              selfTopInt (I := I) (M := M) g T hδ_lt hδ hδZ -
              deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g).toSection x) ≤
          (K * (δ / (1 - δ) ^ 2)) ^ 2 := by
  obtain ⟨KP, hKP, hPb⟩ := metricPrincipalDefect_cap (I := I) (M := M) g
  obtain ⟨KR, hKR, hRb⟩ := ricciTop_cap (I := I) (M := M) g
  let KL := 4 * deTurckArmFibreConst (Module.finrank ℝ E)
  let K0 := 4 * KL ^ 2 + 4 * KP ^ 2 + 8 * KR ^ 2
  have hK0 : 0 ≤ K0 := by positivity
  refine ⟨Real.sqrt K0, Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδ_lt hδ hδZ x
  let Φ := rhsDecompositionTop (I := I) (M := M) g T hδ hδZ
  let Ψ := ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ
  let C := deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hΦ := rhsDecompositionTop_joint (I := I) (M := M)
    g T hδ_lt hδ hδZ
  have hΨ := selfTop_joint (I := I) (M := M) g T hδ hδZ
  have hC := arm_const (I := I) (M := M) g (δ := δ) (δ' := δ) C
  have hKern := threeArmJoint_sub (I := I) (M := M) g _ _
    (threeArmJoint_add (I := I) (M := M) g _ _ hΦ hΨ) hC
  let r1 := δ / (1 - δ)
  let r2 := δ / (1 - δ) ^ 2
  have hr1 : 0 ≤ r1 := div_nonneg hδ0 (by linarith)
  have hr2 : 0 ≤ r2 := div_nonneg hδ0 (sq_nonneg _)
  have hr12 : r1 ≤ r2 := by
    have hb : 0 < 1 - δ := by linarith
    rw [div_le_div_iff₀ hb (sq_pos_of_pos hb)]
    nlinarith only [mul_nonneg (sq_nonneg δ) (le_of_lt hb)]
  apply path_add_sub_cap (I := I) (M := M) g 4 hSI Φ Ψ C
    hΦ hΨ hKern x (Real.sqrt K0 * r2)
    (mul_nonneg (Real.sqrt_nonneg _) hr2)
  intro s hs
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  let P := convexPerturbation (I := I) g T 0 s
  have hsmem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (u v : TangentSpace I y),
      gm.inner y u v = g.inner y u v +
        ccTensorBilinSymm (I := I) g P y u v :=
    fun y u v => metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hδ hδZ hsmem y u v
  have hP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    convert convexPerturbation_gFibreOpBound
      (I := I) (M := M) g T 0 hδ hδZ hs.1 hs.2 using 1
    all_goals ring
  have hL := lieDecomposition2_cap (I := I) (M := M)
    g T hδ_lt hδ0 hδ hδZ hs x
  have hP1 := hPb gm P hδ_lt hδ0 htie hP x
  have hR1 := hRb T hT hδ_le hδ0 hδ hδZ s hs x
  have hP2 := hP1.trans (pow_le_pow_left₀
    (mul_nonneg hKP hr1) (mul_le_mul_of_nonneg_left hr12 hKP) 2)
  have hR2 := hR1.trans (pow_le_pow_left₀
    (mul_nonneg hKR hr1) (mul_le_mul_of_nonneg_left hr12 hKR) 2)
  have hRs : riemannianFiberNormSq (I := I) (M := M) g 4 2 x
      (((-2 * s : ℝ) • ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T).toSection x) ≤
        4 * (KR * r2) ^ 2 := by
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul]
    calc
      (-2 * s) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          ((ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T).toSection x) ≤
        4 * riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          ((ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T).toSection x) := by
            apply mul_le_mul_of_nonneg_right
              (by nlinarith only [hs.1, hs.2])
              (riemannianFiberNormSq_nonneg
                (I := I) (M := M) g 4 2 x _)
      _ ≤ 4 * (KR * r2) ^ 2 := mul_le_mul_of_nonneg_left hR2 (by norm_num)
  rw [topKernel_eq (I := I) (M := M) g T hδ hδZ s]
  have hAB := riemannianFiberNormSq_add_le (I := I) (M := M) g 4 2 x
    ((lieDecomposition2 (I := I) (M := M) g T hδ hδZ s).toSection x)
    ((deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gm -
      deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g).toSection x)
  have hABC := riemannianFiberNormSq_add_le (I := I) (M := M) g 4 2 x
    ((lieDecomposition2 (I := I) (M := M) g T hδ hδZ s +
      (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gm -
        deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g)).toSection x)
    (((-2 * s : ℝ) • ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T).toSection x)
  have htarget : (Real.sqrt K0 * r2) ^ 2 = K0 * r2 ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hK0]
  rw [htarget]
  dsimp only [KL, K0, r1, r2] at hL hP2 hR2 hRs ⊢
  simp only [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
    Pi.add_apply] at hAB hABC ⊢
  linarith
omit sigmaCompactSpace in
private theorem top_sub_lap
    (g : SmoothRiemannianMetric I M)
    (C : SmoothCcTensor g 4 2) (U : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 4 2 C
          (iteratedCovGrad (I := I) g 0 2 2 U) -
        rawTensorConnLapSmooth (I := I) g 0 2 U =
      operatorFieldApply (I := I) (M := M) g 4 2
          (C - deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g)
          (iteratedCovGrad (I := I) g 0 2 2 U) +
        operatorFieldApply (I := I) (M := M) g 2 2
          (metricPrincipalDefectCurvCoeff (I := I) g g) U := by
  have hlap : rawTensorConnLapSmooth (I := I) g 0 2 U =
      operatorFieldApply (I := I) (M := M) g 4 2
        (cometricDoubleTraceCoefficient (I := I) (M := M) g g)
        (iteratedCovGrad (I := I) g 0 2 2 U) := by
    apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
    intro x
    apply ContinuousMultilinearMap.ext
    intro v
    exact rawTensorConnLapSmooth_eq_operatorFieldApplication_cometricDoubleTrace
      (I := I) (M := M) g U x v
  have hcurv := metricPrincipalDefect_curv_fold
    (I := I) (M := M) g g U
  rw [operatorFieldApplication_sub_left] at hcurv
  simp only [iteratedCovGrad_zero] at hcurv
  rw [hlap, operatorFieldApplication_sub_left, ← hcurv]
  abel

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] in
private theorem jet_term_le
    (g : SmoothRiemannianMetric I M) {r s q m : ℕ}
    (hqm : q ≤ m) (S : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 ≤
      covariantJetNormSq (I := I) (M := M) g m S := by
  unfold covariantJetNormSq
  exact Finset.single_le_sum
    (fun j _ => sq_nonneg
      ‖iteratedCovGrad (I := I) g r s j S‖)
    (Finset.mem_range.mpr (by omega))

omit [NeZero (Module.finrank ℝ E)] in
private theorem path_add_sub_h2
    (g : SmoothRiemannianMetric I M) (r : ℕ)
    {δ δ' : ℝ}
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (Φ Ψ : ℝ → SmoothCcTensor g r 2) (C : SmoothCcTensor g r 2)
    (hΦ : linearizedRicciThreeArmHjoint (I := I) (M := M) g r Φ
      (δ := δ) (δ' := δ'))
    (hΨ : linearizedRicciThreeArmHjoint (I := I) (M := M) g r Ψ
      (δ := δ) (δ' := δ'))
    (hK : linearizedRicciThreeArmHjoint (I := I) (M := M) g r
      (fun t => Φ t + Ψ t - C) (δ := δ) (δ' := δ'))
    (B : ℝ)
    (hcap : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      covariantJetNormSq (I := I) (M := M) g 2 (Φ t + Ψ t - C) ≤ B ^ 2) :
    covariantJetNormSq (I := I) (M := M) g 2
        (pathIntegralCoeffField (I := I) (M := M) g r 2 Φ
              (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
              metricPerturbationPathDomain_isOpen hSI hΦ +
          pathIntegralCoeffField (I := I) (M := M) g r 2 Ψ
              (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
              metricPerturbationPathDomain_isOpen hSI hΨ -
          C) ≤ B ^ 2 := by
  let K : ℝ → SmoothCcTensor g r 2 := fun t => Φ t + Ψ t - C
  let PK := pathIntegralCoeffField (I := I) (M := M) g r 2 K
    (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    metricPerturbationPathDomain_isOpen hSI hK
  have heq :
      pathIntegralCoeffField (I := I) (M := M) g r 2 Φ
            (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
            metricPerturbationPathDomain_isOpen hSI hΦ +
          pathIntegralCoeffField (I := I) (M := M) g r 2 Ψ
            (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
            metricPerturbationPathDomain_isOpen hSI hΨ -
          C = PK := by
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro y
    apply TensorRSSpace.toModel_injective
    have hcΦ := jointContMDiff_toModel_continuous_slice
      (I := I) g r 2 Φ
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hΦ y
    have hcΨ := jointContMDiff_toModel_continuous_slice
      (I := I) g r 2 Ψ
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hΨ y
    have hIΦ : IntervalIntegrable (fun t : ℝ =>
        TensorRSSpace.toModel ((Φ t).toSection y))
        MeasureTheory.volume 0 1 :=
      (hcΦ.mono hSI).intervalIntegrable
    have hIΨ : IntervalIntegrable (fun t : ℝ =>
        TensorRSSpace.toModel ((Ψ t).toSection y))
        MeasureTheory.volume 0 1 :=
      (hcΨ.mono hSI).intervalIntegrable
    dsimp only [PK]
    simp only [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub,
      ContMDiffSection.coe_add, ContMDiffSection.coe_sub,
      Pi.add_apply, Pi.sub_apply, TensorRSSpace.toModel_add,
      TensorRSSpace.toModel_sub]
    rw [pathIntegralCoeffField_toModel (I := I) (M := M) g r 2 Φ
        (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
        metricPerturbationPathDomain_isOpen hSI hΦ y,
      pathIntegralCoeffField_toModel (I := I) (M := M) g r 2 Ψ
        (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
        metricPerturbationPathDomain_isOpen hSI hΨ y,
      pathIntegralCoeffField_toModel (I := I) (M := M) g r 2 K
        (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
        metricPerturbationPathDomain_isOpen hSI hK y]
    simp only [K, SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub,
      ContMDiffSection.coe_add, ContMDiffSection.coe_sub,
      Pi.add_apply, Pi.sub_apply, TensorRSSpace.toModel_add,
      TensorRSSpace.toModel_sub]
    rw [intervalIntegral.integral_sub (hIΦ.add hIΨ)
        intervalIntegrable_const,
      intervalIntegral.integral_add hIΦ hIΨ,
      intervalIntegral.integral_const]
    norm_num
  rw [heq]
  simpa only [PK, covariantJetNormSq, Nat.reduceAdd] using
    path_jetL2_le (I := I) (M := M) g r 2 2 K
      (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
      metricPerturbationPathDomain_isOpen hSI hK hcap

omit [BoundarylessManifold I M] in
private theorem jet2_fiber
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : SmoothCcTensor g r s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r s x
            (A.toSection x) ≤
          C ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 A := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g r s
  refine ⟨C, hC, ?_⟩
  intro A x
  have hrange :
      Finset.range (Module.finrank ℝ E / 2 + 2) =
        Finset.range 3 := by
    rw [hDim]
  have h := hbound A x
  rw [hrange] at h
  simpa only [covariantJetNormSq, Nat.reduceAdd] using h

private theorem trace_h2_rf
    (p : ℕ) (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (σ : Equiv.Perm (Fin (p + 2))),
      covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g g₁ p σ) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  classical
  let _ : IsFiniteMeasure
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  obtain ⟨C, hC0, hC⟩ :=
    trace_grid_rf (I := I) (M := M) p g hδ₀
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀0 : 0 ≤ Λ₀ :=
    mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨G, hG0, hG⟩ :=
    antidiagonalTupleGrid_integral_radiusFree
      (I := I) (M := M) g hΛ₀0
  let K : ℝ :=
    ∑ q ∈ Finset.range 3,
      C q * ∑ k ∈ Finset.range (q + 1), G k
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    exact Finset.sum_nonneg fun q _ =>
      mul_nonneg (hC0 q) (Finset.sum_nonneg fun k _ => hG0 k)
  refine ⟨K, hK0, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ σ
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symm_eq_self (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2 := by
    intro x
    rw [← hsymm]
    exact riemannianFiberNormSq_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  have hAG : ∀ k : ℕ,
      MeasureTheory.Integrable
          (fun x => Combinatorics.antidiagonalTupleGrid
            (fun j => riemannianFiberNormSq
              (I := I) (M := M) g 0 (2 + j) x
              ((iteratedCovGrad (I := I) g 0 2 j P).toSection x)) k)
          (riemannianVolumeMeasure (I := I) (M := M) g) ∧
        (∫ x, Combinatorics.antidiagonalTupleGrid
            (fun j => riemannianFiberNormSq
              (I := I) (M := M) g 0 (2 + j) x
              ((iteratedCovGrad (I := I) g 0 2 j P).toSection x)) k
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
          G k *
            (1 + ‖iteratedCovGrad (I := I) g 0 2 k P‖ ^ 2) := by
    intro k
    have hexpand :
        (fun x => Combinatorics.antidiagonalTupleGrid
          (fun j => riemannianFiberNormSq
            (I := I) (M := M) g 0 (2 + j) x
            ((iteratedCovGrad (I := I) g 0 2 j P).toSection x)) k) =
          (fun x => ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq
                  (I := I) (M := M) g 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g 0 2
                    (e m) P).toSection x)) := by
      funext x
      rw [Combinatorics.antidiagonalTupleGrid]
    rw [hexpand]
    exact hG P hsup k
  have hper : ∀ q : ℕ, q ≤ 2 →
      ‖iteratedCovGrad (I := I) g (p + 2) p q
          (reindexedPureTrace (I := I) (M := M) g g₁ p σ)‖ ^ 2 ≤
        (C q * ∑ k ∈ Finset.range (q + 1), G k) *
          (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
    intro q hq
    let W : M → ℝ := fun x =>
      ∑ k ∈ Finset.range (q + 1),
        Combinatorics.antidiagonalTupleGrid
          (fun j => riemannianFiberNormSq
            (I := I) (M := M) g 0 (2 + j) x
            ((iteratedCovGrad (I := I) g 0 2 j P).toSection x)) k
    have hWint : MeasureTheory.Integrable W
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      dsimp only [W]
      exact MeasureTheory.integrable_finsetSum _
        (fun k _ => (hAG k).1)
    have hCWint : MeasureTheory.Integrable
        (fun x => C q * W x)
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      hWint.const_mul _
    have hnorm :=
      normSq_le_integral_of_pointwise_fiberNormSq_le_rs
        (I := I) (M := M) g (p + 2) (p + q)
        (iteratedCovGrad (I := I) g (p + 2) p q
          (reindexedPureTrace (I := I) (M := M) g g₁ p σ))
        (fun x => C q * W x) hCWint
        (fun x => by
          simpa only [W] using
            hC g₁ P htie hδ_le hδ0 hδ σ q x)
    rw [MeasureTheory.integral_const_mul] at hnorm
    refine le_trans hnorm ?_
    have hWbd : (∫ x, W x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
        (∑ k ∈ Finset.range (q + 1), G k) *
          (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
      dsimp only [W]
      rw [MeasureTheory.integral_finsetSum _
        (fun k _ => (hAG k).1), Finset.sum_mul]
      refine Finset.sum_le_sum fun k hk => ?_
      refine le_trans (hAG k).2 ?_
      apply mul_le_mul_of_nonneg_left _ (hG0 k)
      have hkq : k ≤ q := by
        exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hterm :=
        jet_term_le (I := I) (M := M) g
          (le_trans hkq hq) P
      linarith
    calc
      C q * (∫ x, W x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))
          ≤ C q * ((∑ k ∈ Finset.range (q + 1), G k) *
            (1 + covariantJetNormSq (I := I) (M := M) g 2 P)) :=
        mul_le_mul_of_nonneg_left hWbd (hC0 q)
      _ = (C q * ∑ k ∈ Finset.range (q + 1), G k) *
          (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by ring
  unfold covariantJetNormSq
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun q hq =>
    hper q (by
      have : q < 3 := Finset.mem_range.mp hq
      omega)

private theorem conn_h2_rf
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) g₁ g) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) := by
  classical
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀0 : 0 ≤ Λ₀ :=
    mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨Flow, hFlow0, hFlow⟩ :=
    connectionDifferenceSection_lowOrder_jetL2_radiusFree
      (I := I) (M := M) g
        (2 * Module.finrank ℝ E + 10) hδ₀ hΛ₀0
  refine ⟨Flow 2, hFlow0 2, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symm_eq_self (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2 := by
    intro x
    rw [← hsymm]
    exact riemannianFiberNormSq_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  simpa only [covariantJetNormSq, Nat.reduceAdd] using
    hFlow g₁ P htie hδ_le hδ0 hδ hsup 2 (by omega)

private theorem slot_l2
    (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) i
        (slotExtend (I := I) (M := M) g r s Φ)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) *
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
      ((iteratedCovGrad (I := I) g r s i Φ).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i Φ)).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (r + 1) ((s + 1) + i)
    (iteratedCovGrad (I := I) g (r + 1) (s + 1) i
      (slotExtend (I := I) (M := M) g r s Φ))
    F hF (fun x =>
      riemannianFiberNormSq_iteratedCovGrad_slotExtend_le
        (I := I) (M := M) g r s Φ i x)
  have hint : (∫ x,
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i Φ).toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g r (s + i)]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

private theorem slot_h2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g r s Φ) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 2 Φ := by
  unfold covariantJetNormSq
  calc
    ∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) i
          (slotExtend (I := I) (M := M) g r s Φ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 3, (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        slot_l2 (I := I) (M := M) g r s i Φ
    _ = (Module.finrank ℝ E : ℝ) *
        ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
      rw [Finset.mul_sum]

omit [NeZero (Module.finrank ℝ E)] in
private theorem reindex_h2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (ρ : Equiv.Perm (Fin r)) :
    covariantJetNormSq (I := I) (M := M) g 2
        (reindexCoeffGen (I := I) (M := M) g r s Φ ρ) =
      covariantJetNormSq (I := I) (M := M) g 2 Φ := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedCovGrad_reindexCoeffGen,
    norm_reindexCoeffGen_eq]

private theorem app_h2_mul
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        covariantJetNormSq (I := I) (M := M) g 2
            (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
          C * covariantJetNormSq (I := I) (M := M) g 2 Φ *
            covariantJetNormSq (I := I) (M := M) g 2 W := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    operator_field_composition_h2_h2_to_h2_bound (I := I) (M := M) hDim g p r c
  refine ⟨C₀ ^ 2, sq_nonneg _, ?_⟩
  intro Φ W
  have hΦ0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 Φ :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hW0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 W :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsΦ :
      Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 Φ) ^ 2 =
        covariantJetNormSq (I := I) (M := M) g 2 Φ :=
    Real.sq_sqrt hΦ0
  have hsW :
      Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 W) ^ 2 =
        covariantJetNormSq (I := I) (M := M) g 2 W :=
    Real.sq_sqrt hW0
  have h := happ Φ W
    (Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 Φ))
    (Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 W))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (by
      unfold covariantJetNormSq
      exact le_of_eq hsΦ.symm)
    (by
      unfold covariantJetNormSq
      exact le_of_eq hsW.symm)
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
      (C₀ *
        Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 Φ) *
        Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 W)) ^ 2 := by
      simpa only [covariantJetNormSq, Nat.reduceAdd] using h
    _ = C₀ ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 Φ *
        covariantJetNormSq (I := I) (M := M) g 2 W := by
      rw [mul_pow, mul_pow, hsΦ, hsW]

private theorem app_quad
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g 2 2) (W : SmoothCcTensor g 0 2)
        (B R A : ℝ), 0 ≤ B → 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 Φ ≤ (B * A ^ 2) ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2
            (operatorFieldApply (I := I) (M := M) g 2 2 Φ W) ≤
          (C * B * R * A ^ 2) ^ 2 := by
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 2 2
  let C : ℝ := Real.sqrt Ca
  refine ⟨C, Real.sqrt_nonneg _, ?_⟩
  intro Φ W B R A hB hR hA hΦ hW
  have hW0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 W :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hraw :
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2 Φ W) ≤
        Ca * (B * A ^ 2) ^ 2 * R ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2 Φ W) ≤
        Ca * covariantJetNormSq (I := I) (M := M) g 2 Φ *
          covariantJetNormSq (I := I) (M := M) g 2 W := by
            simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using happ Φ W
      _ ≤ Ca * (B * A ^ 2) ^ 2 * R ^ 2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hΦ hCa) hW
          hW0
          (mul_nonneg hCa (sq_nonneg (B * A ^ 2)))
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2 Φ W) ≤
      Ca * (B * A ^ 2) ^ 2 * R ^ 2 := hraw
    _ = (C * B * R * A ^ 2) ^ 2 := by
      rw [show Ca = C ^ 2 by
        simpa only [C] using (Real.sq_sqrt hCa).symm]
      ring

structure LowerScaleActionCoefficients
    (g : SmoothRiemannianMetric I M) where
  zeroOrderCoefficient : SmoothCcTensor g 2 2
  firstOrderCoefficient : SmoothCcTensor g 3 2
  secondOrderCoefficient : SmoothCcTensor g 4 2

noncomputable def LowerScaleActionCoefficients.firstOrderAction
    {g : SmoothRiemannianMetric I M} (A : LowerScaleActionCoefficients g)
    (W : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 2 :=
  operatorFieldApply (I := I) (M := M) g 2 2 A.zeroOrderCoefficient W +
    operatorFieldApply (I := I) (M := M) g 3 2 A.firstOrderCoefficient
      (iteratedCovGrad (I := I) g 0 2 1 W)

noncomputable def LowerScaleActionCoefficients.secondOrderAction
    {g : SmoothRiemannianMetric I M} (A : LowerScaleActionCoefficients g)
    (W : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 2 :=
  operatorFieldApply (I := I) (M := M) g 4 2 A.secondOrderCoefficient
    (iteratedCovGrad (I := I) g 0 2 2 W)

noncomputable def lowerScaleActionCoefficients
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    LowerScaleActionCoefficients g where
  zeroOrderCoefficient := selfLowInt (I := I) (M := M) g g_bg T
      hδ_lt hδ hδZ + metricPrincipalDefectCurvCoeff (I := I) g g
  firstOrderCoefficient := ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M)
      g g_bg T 0 hδ_lt hδ hδ_lt hδZ
  secondOrderCoefficient := rhsDecompositionTopInt (I := I) (M := M)
      g T hδ_lt hδ hδZ +
    selfTopInt (I := I) (M := M) g T hδ_lt hδ hδZ -
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g

namespace RicciDeTurckLowOrder

def connectionDifferenceLowOrderPermutation : Equiv.Perm (Fin 3) :=
  ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩

def ricciConnectionDifferenceDerivativeCyclicPermutation : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 3, 0], ![3, 0, 1, 2], by decide, by decide⟩

def ricciConnectionDifferenceDerivativeFirstPairSwap : Equiv.Perm (Fin 4) :=
  ⟨![1, 0, 2, 3], ![1, 0, 2, 3], by decide, by decide⟩

noncomputable def connectionDifferenceLowOrderOperator
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 3 3
    (permCoeff (I := I) (M := M) g connectionDifferenceLowOrderPermutation)
    (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
      (slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M) g gm))
      (koszulOp (I := I) (M := M) g))

omit sigmaCompactSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem connectionDifferenceLowOrderOperator_apply
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    ccOperatorFieldComp (I := I) (M := M) g 0 3 3
        (connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)
        (covGrad (I := I) (M := M) g 0 2 T) =
      metricLoweredConnectionDifferenceCoefficient (I := I) g gm :=
  connLowOp_app (I := I) (M := M) g gm T hT htie

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem connectionDifferenceLowOrderOperator_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 3 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 3 3 ℝ E)
        (E := fun x : M => TensorRSSpace 3 3 I x) p.1
        ((connectionDifferenceLowOrderOperator (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ
        metricPerturbationPathDomain (δ := δ) (δ' := δ)) := by
  exact IntrinsicSpectral.connectionDifferenceLowOrderOperator_joint
    (I := I) (M := M) g T hδ hδZ

noncomputable def ricciConnectionPrincipalCoefficient
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 4 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 4 4 4
    (permCoeff (I := I) (M := M) g ricciConnectionDifferenceDerivativeCyclicPermutation)
    (slotExtend (I := I) (M := M) g 3 3
      (connectionDifferenceLowOrderOperator (I := I) (M := M) g gm))

noncomputable def ricciConnectionDerivativeCoefficient
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 4 4
    (permCoeff (I := I) (M := M) g ricciConnectionDifferenceDerivativeCyclicPermutation)
    (covGrad (I := I) (M := M) g 3 3
      (connectionDifferenceLowOrderOperator (I := I) (M := M) g gm))

noncomputable def ricciConnectionDifferenceDerivativeMetricWeight
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 0 2 :=
  operatorFieldApply (I := I) (M := M) g 2 2
    (slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gm)) W

noncomputable def ricciConnectionDifferenceDerivativeContractionMonomial
    (g gm : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) : SmoothCcTensor g 2 2 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 2 2
    (decompositionKernelContractionMonomialField (I := I) (M := M) g g G σ)
    (slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gm))

noncomputable def ricciConnectionDifferenceDerivativeContraction
    (g gm : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4) :
    SmoothCcTensor g 2 2 :=
  ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gm G ricciConnectionDifferenceDerivativeCyclicPermutation -
    ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gm G ricciConnectionDifferenceDerivativeFirstPairSwap

noncomputable def ricciConnectionDifferenceDerivativeTransposedMonomial
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (σ : Equiv.Perm (Fin 4)) : SmoothCcTensor g 4 2 :=
  curvatureDecompositionMonomialCoeffField (I := I) (M := M) g g
    (ccTensorUnitValueSection (I := I) (M := M) g
      (ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm W))
    (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g
      (ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm W)) σ

noncomputable def ricciConnectionDifferenceDerivativeTransposedCoefficient
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 4 2 :=
  ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M) g gm W ricciConnectionDifferenceDerivativeCyclicPermutation -
    ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M) g gm W ricciConnectionDifferenceDerivativeFirstPairSwap

omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem ricciConnectionDifferenceDerivativeTransposedCoefficient_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ : 0 ≤ δ)
    (hTδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        ((ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hTδ hδZ s) T).toSection x) ≤
      (2 * deTurckArmFibreConst (Module.finrank ℝ E) *
        (δ / (1 - δ))) ^ 2 := by
  exact IntrinsicSpectral.ricciConnectionDifferenceDerivativeTransposedCoefficient_fiberNormSq_le
    (I := I) (M := M) g T hT hδ_lt hδ hTδ hδZ s hs x

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem daMono_swap
    (g gm : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gm G σ) W =
      operatorFieldApply (I := I) (M := M) g 4 2
        (ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M) g gm W σ) G := by
  rw [ricciConnectionDifferenceDerivativeContractionMonomial, ← operatorFieldApplication_assoc]
  exact mono_trans (I := I) (M := M) g G σ
    (ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm W)

omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
omit sigmaCompactSpace in
private theorem daContr_swap
    (g gm : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ricciConnectionDifferenceDerivativeContraction (I := I) (M := M) g gm G) W =
      operatorFieldApply (I := I) (M := M) g 4 2
        (ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm W) G := by
  rw [ricciConnectionDifferenceDerivativeContraction, ricciConnectionDifferenceDerivativeTransposedCoefficient, operatorFieldApplication_sub_left, operatorFieldApplication_sub_left,
    daMono_swap, daMono_swap]

noncomputable def ricciConnectionDifferenceTopOrderCoefficient
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 4 2 :=
  ccOperatorFieldComp (I := I) (M := M) g 4 4 2
    (ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm T)
    (ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm)

noncomputable def ricciCovariantDerivativeConnectionDifferenceLowOrder
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 2 2 :=
  ricciConnectionDifferenceDerivativeContraction (I := I) (M := M) g gm
    (ccOperatorFieldComp (I := I) (M := M) g 0 3 4
      (ricciConnectionDerivativeCoefficient (I := I) (M := M) g gm)
      (covGrad (I := I) (M := M) g 0 2 T))

noncomputable def ricciConnectionDerivativeTransposedCoefficient
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 2 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 4 2
    (ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm W)
    (ricciConnectionDerivativeCoefficient (I := I) (M := M) g gm)

omit [BoundarylessManifold I M] in
omit sigmaCompactSpace in
theorem ricciCovariantDerivativeConnectionDifferenceLowOrder_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gm P) W =
      operatorFieldApply (I := I) (M := M) g 3 2
        (ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gm W)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [ricciCovariantDerivativeConnectionDifferenceLowOrder, daContr_swap]
  simp only [ricciConnectionDerivativeTransposedCoefficient, operatorFieldComposition_zero_eq_operatorFieldApply]
  rw [operatorFieldApplication_assoc]

omit sigmaCompactSpace in
omit [NeZero (Module.finrank ℝ E)] in
private theorem dagLow_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointRS (I := I) g 3 4
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => ricciConnectionDerivativeCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)) := by
  have hc := connectionDifferenceLowOrderOperator_joint (I := I) (M := M) g T hδ hδZ
  have hd := covGrad_step_jointContMDiffOn (I := I) (M := M)
    g 3 3
    (fun t => connectionDifferenceLowOrderOperator (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hδ hδZ t))
    (metricPerturbationPathDomain (δ := δ) (δ' := δ)) hc
  have hd' : JointRS (I := I) g 3 4
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => covGrad (I := I) (M := M) g 3 3
        (connectionDifferenceLowOrderOperator (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ t))) := by
    simpa only [Nat.reduceAdd] using hd
  have hp := joint_const (I := I) (M := M)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ)) g
    (permCoeff (I := I) (M := M) g ricciConnectionDifferenceDerivativeCyclicPermutation)
  have hout := joint_app (I := I) (M := M) g _ _ hp hd'
  simpa only [ricciConnectionDerivativeCoefficient] using hout

omit sigmaCompactSpace in
theorem ricciConnectionDerivativeTransposedCoefficient_joint
    (g : SmoothRiemannianMetric I M) (T W : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 3
      (fun t => ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) W)
      (δ := δ) (δ' := δ) := by
  have hA : JointRS (I := I) g 4 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) W) := by
    have hAraw := daTrans_joint (I := I) (M := M) g T W hδ hδZ
    rw [linearizedRicciThreeArmHjoint] at hAraw
    exact hAraw
  have hB := dagLow_joint (I := I) (M := M) g T hδ hδZ
  have hout := joint_app (I := I) (M := M) g _ _ hA hB
  simpa only [linearizedRicciThreeArmHjoint, ricciConnectionDerivativeTransposedCoefficient] using hout

noncomputable def ricciConnectionDifferenceLowOrderCoefficient
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 2 2 :=
  ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gm +
    ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gm T

noncomputable def symmetrizedRicciConnectionDifferenceLowOrderCoefficient
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 2 2 :=
  ccInputSlotSymm (I := I) (M := M) g
    (ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm T)

noncomputable def ricciConnectionDifferenceSecondDerivativeContraction
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 2 2 :=
  ricciConnectionDifferenceDerivativeContraction (I := I) (M := M) g gm
    (ccOperatorFieldComp (I := I) (M := M) g 0 4 4
      (ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm)
      (iteratedCovGrad (I := I) g 0 2 2 T))

noncomputable def reducedRicciConnectionDifferenceLowOrderCoefficient
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 2 2 :=
  ccInputSlotSymm (I := I) (M := M) g
    (linearizedRicciConnectionDifferenceOrder0CoeffField
        (I := I) (M := M) g gm -
      ricciConnectionDifferenceSecondDerivativeContraction (I := I) (M := M) g gm T)

noncomputable def ricciDeTurckSelfTopOrderCoefficient
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 4 2 :=
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  (-2 * s : ℝ) • ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T +
    (-1 : ℝ) • ricciDecomposition2 (I := I) (M := M) g T hδ hδZ s

noncomputable def pathIntegrand
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 2 2 :=
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  (-2 : ℝ) • reducedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm (s • T) +
    deTurckLieCoeffField (I := I) (M := M) g gm g_bg +
    lieCorrectionZeroField (I := I) (M := M) g gm g_bg -
    deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
      lieDecompositionQ lieDecompositionEps s

omit sigmaCompactSpace in
theorem self_remainder_decomposition
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (rhsDecomposition0 (I := I) (M := M) g g_bg T hδ hδZ s) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (pathIntegrand (I := I) (M := M) g g_bg T hδ hδZ s) T +
        operatorFieldApply (I := I) (M := M) g 4 2
          (ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ s)
          (iteratedCovGrad (I := I) g 0 2 2 T) := by
  exact IntrinsicSpectral.rhs_self_decomposition
    (I := I) (M := M) g g_bg T hT hδ_lt hδ hδZ hs

omit sigmaCompactSpace in
theorem selfLow_good
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    pathIntegrand (I := I) (M := M) g g_bg T hδ hδZ s =
      let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
      (-2 : ℝ) • symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm (s • T) +
        deTurckLieCoeffField (I := I) (M := M) g gm g_bg +
        lieCorrectionZeroField (I := I) (M := M) g gm g_bg -
        deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
          lieDecompositionQ lieDecompositionEps s := by
  exact IntrinsicSpectral.rhsSelf_good
    (I := I) (M := M) g g_bg T hT hδ_lt hδ hδZ hs

omit [BoundarylessManifold I M] in
omit sigmaCompactSpace in
theorem selfTop_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 4
      (ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ)
      (δ := δ) (δ' := δ) := by
  exact IntrinsicSpectral.selfTop_joint
    (I := I) (M := M) g T hδ hδZ

omit sigmaCompactSpace in
theorem selfLow_joint
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (pathIntegrand (I := I) (M := M) g g_bg T hδ hδZ)
      (δ := δ) (δ' := δ) := by
  exact IntrinsicSpectral.selfLow_joint
    (I := I) (M := M) g g_bg T hδ hδZ

noncomputable def selfTopInt
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 4 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 4 2
    (ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (selfTop_joint (I := I) (M := M) g T hδ hδZ)

noncomputable def selfLowInt
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 2 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 2 2
    (pathIntegrand (I := I) (M := M) g g_bg T hδ hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (selfLow_joint (I := I) (M := M) g g_bg T hδ hδZ)

omit sigmaCompactSpace in
theorem selfLowInt_toModel
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) (x : M) :
    TensorRSSpace.toModel
        ((selfLowInt (I := I) (M := M) g g_bg T hδ_lt hδ hδZ).toSection x) =
      ∫ s in (0 : ℝ)..1, TensorRSSpace.toModel
        ((pathIntegrand (I := I) (M := M) g g_bg T hδ hδZ s).toSection x) := by
  unfold selfLowInt
  exact pathIntegralCoeffField_toModel (I := I) (M := M) g 2 2 _ _ _ _ _ x

omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem topKernel_eq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
    rhsDecompositionTop (I := I) (M := M) g T hδ hδZ s +
          ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ s -
          deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g =
      lieDecomposition2 (I := I) (M := M) g T hδ hδZ s +
        (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gm -
          deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g) +
        (-2 * s : ℝ) • ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T := by
  simp only [rhsDecompositionTop, rhsDecomposition2, ricciDeTurckSelfTopOrderCoefficient]
  module

theorem secondOrderCoefficient_eq
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    (lowerScaleActionCoefficients (I := I) (M := M) g g_bg T hδ_lt hδ hδZ).secondOrderCoefficient =
      rhsDecompositionTopInt (I := I) (M := M)
          g T hδ_lt hδ hδZ +
        selfTopInt (I := I) (M := M) g T hδ_lt hδ hδZ -
        deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g := by
  rfl

theorem zeroOrderCoefficient_eq
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    (lowerScaleActionCoefficients (I := I) (M := M) g g_bg T hδ_lt hδ hδZ).zeroOrderCoefficient =
      selfLowInt (I := I) (M := M) g g_bg T hδ_lt hδ hδZ +
        metricPrincipalDefectCurvCoeff (I := I) g g := by
  rfl

theorem firstOrderCoefficient_eq
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    (lowerScaleActionCoefficients (I := I) (M := M) g g_bg T hδ_lt hδ hδZ).firstOrderCoefficient =
      ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M)
        g g_bg T 0 hδ_lt hδ hδ_lt hδZ := by
  rfl

end RicciDeTurckLowOrder

theorem lowData_split
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
      let A := lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ;
        deTurckSmoothRemainder (I := I) g g_bg T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδ -
            deTurckSmoothRemainder (I := I) g g_bg
              (0 : SmoothCcTensor g 0 2)
              (lt_of_le_of_lt hδ_le (by norm_num)) hδZ =
          A.secondOrderAction (I := I) (M := M) T + A.firstOrderAction (I := I) (M := M) T ∧
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              (A.secondOrderCoefficient.toSection x) ≤
            (K * (δ / (1 - δ) ^ 2)) ^ 2 := by
  obtain ⟨K, hK, hcap⟩ := secondOrderCoefficient_fibre_bound (I := I) (M := M) g
  refine ⟨K, hK, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let A := lowerScaleActionCoefficients (I := I) (M := M)
    g g_bg T hδ_lt hδ hδZ
  refine ⟨?_, fun x => by
    simpa only [A, lowerScaleActionCoefficients] using
      hcap T hT hδ_le hδ0 hδ_lt hδ hδZ x⟩
  change
    (deTurckRHSAtMetricPerturbation (I := I) g g_bg T hδ_lt hδ -
        rawTensorConnLapSmooth (I := I) g 0 2 T) -
      (deTurckRHSAtMetricPerturbation (I := I) g g_bg
          (0 : SmoothCcTensor g 0 2) hδ_lt hδZ -
        rawTensorConnLapSmooth (I := I) g 0 2
          (0 : SmoothCcTensor g 0 2)) = _
  have hlap0 : rawTensorConnLapSmooth (I := I) g 0 2
      (0 : SmoothCcTensor g 0 2) = 0 := by
    have hzero := rawTensorConnLapSmooth_sub
      (I := I) (M := M) g 0 2 T T
    rwa [sub_self, sub_self] at hzero
  rw [hlap0, sub_zero]
  rw [show
    (deTurckRHSAtMetricPerturbation (I := I) g g_bg T hδ_lt hδ -
        rawTensorConnLapSmooth (I := I) g 0 2 T) -
      deTurckRHSAtMetricPerturbation (I := I) g g_bg
        (0 : SmoothCcTensor g 0 2) hδ_lt hδZ =
      (deTurckRHSAtMetricPerturbation (I := I) g g_bg T hδ_lt hδ -
        deTurckRHSAtMetricPerturbation (I := I) g g_bg
          (0 : SmoothCcTensor g 0 2) hδ_lt hδZ) -
        rawTensorConnLapSmooth (I := I) g 0 2 T by abel]
  rw [rhs_sub_zero_decomposition (I := I) (M := M)
    g g_bg T hT hδ_lt hδ hδZ]
  rw [zero_order_decomposition_self (I := I) (M := M)
    g g_bg T hT hδ_lt hδ hδZ]
  rw [show
      (operatorFieldApply (I := I) (M := M) g 2 2
          (selfLowInt (I := I) (M := M) g g_bg T
            hδ_lt hδ hδZ) T +
        operatorFieldApply (I := I) (M := M) g 4 2
          (selfTopInt (I := I) (M := M) g T
            hδ_lt hδ hδZ)
          (iteratedCovGrad (I := I) g 0 2 2 T) +
        operatorFieldApply (I := I) (M := M) g 3 2
          (ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M)
            g g_bg T 0 hδ_lt hδ hδ_lt hδZ)
          (iteratedCovGrad (I := I) g 0 2 1 T) +
        operatorFieldApply (I := I) (M := M) g 4 2
          (rhsDecompositionTopInt (I := I) (M := M)
            g T hδ_lt hδ hδZ)
          (iteratedCovGrad (I := I) g 0 2 2 T)) -
        rawTensorConnLapSmooth (I := I) g 0 2 T =
      (operatorFieldApply (I := I) (M := M) g 4 2
          (rhsDecompositionTopInt (I := I) (M := M)
              g T hδ_lt hδ hδZ +
            selfTopInt (I := I) (M := M) g T
              hδ_lt hδ hδZ)
          (iteratedCovGrad (I := I) g 0 2 2 T) -
        rawTensorConnLapSmooth (I := I) g 0 2 T) +
      (operatorFieldApply (I := I) (M := M) g 2 2
          (selfLowInt (I := I) (M := M) g g_bg T
            hδ_lt hδ hδZ) T +
        operatorFieldApply (I := I) (M := M) g 3 2
          (ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M)
            g g_bg T 0 hδ_lt hδ hδ_lt hδZ)
          (iteratedCovGrad (I := I) g 0 2 1 T)) by
      rw [operatorFieldApplication_add_left]
      abel]
  rw [top_sub_lap (I := I) (M := M) g]
  simp only [lowerScaleActionCoefficients, LowerScaleActionCoefficients.firstOrderAction,
    LowerScaleActionCoefficients.secondOrderAction, operatorFieldApplication_add_left, operatorFieldApplication_sub_left]
  abel

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem pure_eq_trace
    (g g₁ : SmoothRiemannianMetric I M) :
    cometricDoubleTraceCoefficient (I := I) (M := M) g g₁ =
      pureTrace (I := I) (M := M) g g₁ 2 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricDoubleTraceCoefficient_toSection,
    pureTrace_toSection]

private theorem fourtrace_h2_rf
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciCometricFourTraceCastG0 (I := I) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  classical
  obtain ⟨K₀, hK₀, htrace⟩ :=
    trace_h2_rf (I := I) (M := M) 2 g hδ₀0 hδ₀
  refine ⟨22 * K₀, mul_nonneg (by norm_num) hK₀, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  let F : SmoothCcTensor g 4 2 :=
    cometricDoubleTraceCoefficient (I := I) (M := M) g g₁
  let R₁ : SmoothCcTensor g 4 2 :=
    reindexCoeffGen (I := I) (M := M) g 4 2 F
      fourTraceArgPerm0231
  let R₂ : SmoothCcTensor g 4 2 :=
    reindexCoeffGen (I := I) (M := M) g 4 2 F
      fourTraceArgPerm0321
  let R₃ : SmoothCcTensor g 4 2 :=
    reindexCoeffGen (I := I) (M := M) g 4 2 F
      fourTraceArgPerm2301
  have hF :
      covariantJetNormSq (I := I) (M := M) g 2 F ≤
        K₀ * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
    have h :=
      htrace g₁ P hP htie hδ_le hδ0 hδ
        (Equiv.refl (Fin 4))
    rw [reindexedPureTrace, reindex_h2] at h
    simpa only [F, pure_eq_trace (I := I) (M := M) g g₁] using h
  have hR₁ :
      covariantJetNormSq (I := I) (M := M) g 2 R₁ =
        covariantJetNormSq (I := I) (M := M) g 2 F := by
    exact reindex_h2 (I := I) (M := M) g 4 2 F
      fourTraceArgPerm0231
  have hR₂ :
      covariantJetNormSq (I := I) (M := M) g 2 R₂ =
        covariantJetNormSq (I := I) (M := M) g 2 F := by
    exact reindex_h2 (I := I) (M := M) g 4 2 F
      fourTraceArgPerm0321
  have hR₃ :
      covariantJetNormSq (I := I) (M := M) g 2 R₃ =
        covariantJetNormSq (I := I) (M := M) g 2 F := by
    exact reindex_h2 (I := I) (M := M) g 4 2 F
      fourTraceArgPerm2301
  have h12 :
      covariantJetNormSq (I := I) (M := M) g 2 (R₁ + R₂) ≤
        4 * covariantJetNormSq (I := I) (M := M) g 2 F := by
    have h := covariantJetNormSq_add_le (I := I) (M := M) g 2 R₁ R₂
    rw [hR₁, hR₂] at h
    linarith
  have h123 :
      covariantJetNormSq (I := I) (M := M) g 2 (R₁ + R₂ - F) ≤
        10 * covariantJetNormSq (I := I) (M := M) g 2 F := by
    have h := covariantJetNormSq_sub_le (I := I) (M := M) g 2 (R₁ + R₂) F
    have hF0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g F
    nlinarith only [h, h12, hF0]
  have h1234 :
      covariantJetNormSq (I := I) (M := M) g 2
          (R₁ + R₂ - F - R₃) ≤
        22 * covariantJetNormSq (I := I) (M := M) g 2 F := by
    have h := covariantJetNormSq_sub_le (I := I) (M := M) g 2
      (R₁ + R₂ - F) R₃
    rw [hR₃] at h
    have hF0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g F
    nlinarith only [h, h123, hF0]
  have hcomb :
      ricciCometricFourTraceCastG0 (I := I) g g₁ =
        ((1 : ℝ) / 2) • (R₁ + R₂ - F - R₃) := by
    simpa only [F, R₁, R₂, R₃] using
      ricciCometricFourTraceCastG0_eq_reindex_combination
        (I := I) g g₁
  rw [hcomb, covariantJetNormSq_smul]
  have hJ0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (R₁ + R₂ - F - R₃)
  calc
    ((1 : ℝ) / 2) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2 (R₁ + R₂ - F - R₃) ≤
      covariantJetNormSq (I := I) (M := M) g 2 (R₁ + R₂ - F - R₃) := by
        nlinarith only [hJ0]
    _ ≤ 22 * covariantJetNormSq (I := I) (M := M) g 2 F := h1234
    _ ≤ 22 * (K₀ *
        (1 + covariantJetNormSq (I := I) (M := M) g 2 P)) :=
      mul_le_mul_of_nonneg_left hF (by norm_num)
    _ = (22 * K₀) *
        (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by ring

private def H2Poly
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s : ℕ} (n : ℕ) (K : ℝ) (S : SmoothCcTensor g r s) : Prop :=
  0 ≤ K ∧
    covariantJetNormSq (I := I) (M := M) g 2 S ≤
      K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ n

omit [CompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem hp_const
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s : ℕ} (S : SmoothCcTensor g r s) :
    H2Poly (I := I) (M := M) g P 0
      (covariantJetNormSq (I := I) (M := M) g 2 S) S := by
  refine ⟨covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g S, ?_⟩
  rw [pow_zero, mul_one]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem hp_add
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s n : ℕ} {A B : ℝ}
    {S T : SmoothCcTensor g r s}
    (hS : H2Poly (I := I) (M := M) g P n A S)
    (hT : H2Poly (I := I) (M := M) g P n B T) :
    H2Poly (I := I) (M := M) g P n
      (2 * (A + B)) (S + T) := by
  have hX0 : 0 ≤
      (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ n :=
    pow_nonneg (by
      linarith [covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g P]) n
  refine ⟨mul_nonneg (by norm_num) (add_nonneg hS.1 hT.1), ?_⟩
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (S + T) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 S +
          covariantJetNormSq (I := I) (M := M) g 2 T) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 2 S T
    _ ≤ 2 * (A *
          (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ n +
        B * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ n) :=
      mul_le_mul_of_nonneg_left (add_le_add hS.2 hT.2) (by norm_num)
    _ = 2 * (A + B) *
        (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ n := by ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem hp_sub
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s n : ℕ} {A B : ℝ}
    {S T : SmoothCcTensor g r s}
    (hS : H2Poly (I := I) (M := M) g P n A S)
    (hT : H2Poly (I := I) (M := M) g P n B T) :
    H2Poly (I := I) (M := M) g P n
      (2 * (A + B)) (S - T) := by
  refine ⟨mul_nonneg (by norm_num) (add_nonneg hS.1 hT.1), ?_⟩
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (S - T) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 S +
          covariantJetNormSq (I := I) (M := M) g 2 T) :=
      covariantJetNormSq_sub_le (I := I) (M := M) g 2 S T
    _ ≤ 2 * (A *
          (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ n +
        B * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ n) :=
      mul_le_mul_of_nonneg_left (add_le_add hS.2 hT.2) (by norm_num)
    _ = 2 * (A + B) *
        (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ n := by ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem hp_smul
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s n : ℕ} {A : ℝ} {S : SmoothCcTensor g r s}
    (c : ℝ)
    (hS : H2Poly (I := I) (M := M) g P n A S) :
    H2Poly (I := I) (M := M) g P n
      (c ^ 2 * A) (c • S) := by
  refine ⟨mul_nonneg (sq_nonneg _) hS.1, ?_⟩
  rw [covariantJetNormSq_smul]
  calc
    c ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 S ≤
        c ^ 2 * (A *
          (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ n) :=
      mul_le_mul_of_nonneg_left hS.2 (sq_nonneg _)
    _ = c ^ 2 * A *
        (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ n := by ring

omit [CompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem hp_raise
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s n m : ℕ} {A : ℝ} {S : SmoothCcTensor g r s}
    (hnm : n ≤ m)
    (hS : H2Poly (I := I) (M := M) g P n A S) :
    H2Poly (I := I) (M := M) g P m A S := by
  have hbase : (1 : ℝ) ≤
      1 + covariantJetNormSq (I := I) (M := M) g 3 P := by
    linarith [covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g P]
  refine ⟨hS.1, le_trans hS.2 ?_⟩
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hbase hnm) hS.1

omit [NeZero (Module.finrank ℝ E)] in
private theorem hp_reindex
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s n : ℕ} {A : ℝ} {S : SmoothCcTensor g r s}
    (ρ : Equiv.Perm (Fin r))
    (hS : H2Poly (I := I) (M := M) g P n A S) :
    H2Poly (I := I) (M := M) g P n A
      (reindexCoeffGen (I := I) (M := M) g r s S ρ) := by
  refine ⟨hS.1, ?_⟩
  rw [reindex_h2]
  exact hS.2

private theorem hp_slot
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s n : ℕ} {A : ℝ} {S : SmoothCcTensor g r s}
    (hS : H2Poly (I := I) (M := M) g P n A S) :
    H2Poly (I := I) (M := M) g P n
      ((Module.finrank ℝ E : ℝ) * A)
      (slotExtend (I := I) (M := M) g r s S) := by
  have hfr : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
  refine ⟨mul_nonneg hfr hS.1, ?_⟩
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g r s S) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 2 S :=
      slot_h2 (I := I) (M := M) g r s S
    _ ≤ (Module.finrank ℝ E : ℝ) *
        (A * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ n) :=
      mul_le_mul_of_nonneg_left hS.2 hfr
    _ = ((Module.finrank ℝ E : ℝ) * A) *
        (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ n := by ring

private theorem hp_slot2
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s n : ℕ} {A : ℝ} {S : SmoothCcTensor g r s}
    (hS : H2Poly (I := I) (M := M) g P n A S) :
    H2Poly (I := I) (M := M) g P n
      ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * A))
      (slotExtendIter (I := I) (M := M) g r s 2 S) := by
  have h1 := hp_slot (I := I) (M := M) g P hS
  have h2 := hp_slot (I := I) (M := M) g P h1
  simpa only [slotExtendIter, Nat.add_zero, Nat.zero_add,
    Nat.reduceAdd] using h2

private theorem hp_slot3
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s n : ℕ} {A : ℝ} {S : SmoothCcTensor g r s}
    (hS : H2Poly (I := I) (M := M) g P n A S) :
    H2Poly (I := I) (M := M) g P n
      ((Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * A)))
      (slotExtendIter (I := I) (M := M) g r s 3 S) := by
  have h1 := hp_slot (I := I) (M := M) g P hS
  have h2 := hp_slot (I := I) (M := M) g P h1
  have h3 := hp_slot (I := I) (M := M) g P h2
  simpa only [slotExtendIter, Nat.add_zero, Nat.zero_add,
    Nat.reduceAdd] using h3

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem hp_app_of
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {p r c n m : ℕ} {A B : ℝ}
    {Φ : SmoothCcTensor g r c} {W : SmoothCcTensor g p r}
    (C : ℝ) (hC : 0 ≤ C)
    (happ : covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
        C * covariantJetNormSq (I := I) (M := M) g 2 Φ *
          covariantJetNormSq (I := I) (M := M) g 2 W)
    (hΦ : H2Poly (I := I) (M := M) g P n A Φ)
    (hW : H2Poly (I := I) (M := M) g P m B W) :
    H2Poly (I := I) (M := M) g P (n + m) (C * A * B)
      (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) := by
  let X : ℝ := 1 + covariantJetNormSq (I := I) (M := M) g 3 P
  have hX : 0 ≤ X := by
    dsimp only [X]
    linarith [covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g P]
  refine ⟨mul_nonneg (mul_nonneg hC hΦ.1) hW.1, ?_⟩
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
      C * covariantJetNormSq (I := I) (M := M) g 2 Φ *
        covariantJetNormSq (I := I) (M := M) g 2 W := happ
    _ ≤ C * (A * X ^ n) *
        covariantJetNormSq (I := I) (M := M) g 2 W := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hΦ.2 hC)
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g W)
    _ ≤ C * (A * X ^ n) * (B * X ^ m) := by
      exact mul_le_mul_of_nonneg_left hW.2
        (mul_nonneg hC (mul_nonneg hΦ.1 (pow_nonneg hX n)))
    _ = (C * A * B) *
        (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ (n + m) := by
      rw [pow_add]
      simp only [X]
      ring

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

private def ricciQuadraticPermutationSwapZeroOne : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def ricciQuadraticPermutationRotateInputs : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

private def nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo
    (g g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeOneTwo)
    (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g g₁)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroOne)
        (connectionDifferenceContrInsertionInnerField (I := I) g g₁)))

private def reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks
    (g g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapBlocks)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
        (connectionDifferenceContravariantInsertionField (I := I) g g₁)
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroOne)
          (connectionDifferenceContrInsertionInnerField (I := I) g g₁))))
    innerCoreInPerm10

private def nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo
    (g g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeTwo)
    (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g g₁)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationRotateInputs)
        (connectionDifferenceContrInsertionInnerField (I := I) g g₁)))

private def reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo
    (g g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneThreeTwo)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
        (connectionDifferenceContravariantInsertionField (I := I) g g₁)
        (connectionDifferenceContrInsertionInnerField (I := I) g g₁)))
    innerCoreInPerm10

private def bareConnectionDifferenceKernelTerm_cycleZeroOneTwo
    (g g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneTwo)
    (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g g₁)
      (connectionDifferenceContrInsertionInnerField (I := I) g g₁))

private def reindexedNestedConnectionDifferenceKernelTerm_rotateInputs_swapZeroTwo
    (g g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroTwo)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
        (connectionDifferenceContravariantInsertionField (I := I) g g₁)
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricciQuadraticPermutationRotateInputs)
          (connectionDifferenceContrInsertionInnerField (I := I) g g₁))))
    innerCoreInPerm10

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem ricciConnectionDifferenceQuadraticKernel_eq_sum
    (g g₁ : SmoothRiemannianMetric I M) :
    ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g g₁ =
      nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo (I := I) (M := M) g g₁ +
      reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks (I := I) (M := M) g g₁ +
      nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo (I := I) (M := M) g g₁ +
      reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo (I := I) (M := M) g g₁ +
      bareConnectionDifferenceKernelTerm_cycleZeroOneTwo (I := I) (M := M) g g₁ +
      reindexedNestedConnectionDifferenceKernelTerm_rotateInputs_swapZeroTwo (I := I) (M := M) g g₁ := by
  rw [ricciConnectionDifferenceQuadraticKernel]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply congrArg₂ (· + ·)
      · apply congrArg₂ (· + ·)
        · apply congrArg₂ (· + ·) <;> rfl
        · rfl
      · rfl
    · rfl
  · rfl

private theorem ricciConnectionDifferenceQuadratic_secondOrder_radiusFree_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 3 := by
  classical
  obtain ⟨Kc, hKc, hconn⟩ :=
    conn_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Kt, hKt, htrace⟩ :=
    fourtrace_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨C233, hC233, h233⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 3 3
  obtain ⟨C234, hC234, h234⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 3 4
  obtain ⟨C244, hC244, h244⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 4 4
  obtain ⟨C242, hC242, h242⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 4 2
  let fr : ℝ := Module.finrank ℝ E
  let Kinner : ℝ := fr * Kc
  let Kouter : ℝ := fr * (fr * Kc)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hKinner : 0 ≤ Kinner :=
    mul_nonneg hfr hKc
  have hKouter : 0 ≤ Kouter :=
    mul_nonneg hfr hKinner
  let P102 : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroOne)
  let P120 : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationRotateInputs)
  let P3201 : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeOneTwo)
  let P2301 : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapBlocks)
  let P3102 : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeTwo)
  let P1302 : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneThreeTwo)
  let P1203 : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneTwo)
  let P2103 : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroTwo)
  have hP102 : 0 ≤ P102 := by
    exact covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hP120 : 0 ≤ P120 := by
    exact covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hP3201 : 0 ≤ P3201 := by
    exact covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hP2301 : 0 ≤ P2301 := by
    exact covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hP3102 : 0 ≤ P3102 := by
    exact covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hP1302 : 0 ≤ P1302 := by
    exact covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hP1203 : 0 ≤ P1203 := by
    exact covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hP2103 : 0 ≤ P2103 := by
    exact covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  let K102 : ℝ := C233 * P102 * Kinner
  let K120 : ℝ := C233 * P120 * Kinner
  let Kcore0 : ℝ := C234 * Kouter * K102
  let Kcore2 : ℝ := C234 * Kouter * K120
  let Kcore3 : ℝ := C234 * Kouter * Kinner
  let K0 : ℝ := C244 * P3201 * Kcore0
  let K1 : ℝ := C244 * P2301 * Kcore0
  let K2 : ℝ := C244 * P3102 * Kcore2
  let K3 : ℝ := C244 * P1302 * Kcore3
  let K4 : ℝ := C244 * P1203 * Kcore3
  let K5 : ℝ := C244 * P2103 * Kcore2
  let K01 : ℝ := 2 * (K0 + K1)
  let K012 : ℝ := 2 * (K01 + K2)
  let K0123 : ℝ := 2 * (K012 + K3)
  let K01234 : ℝ := 2 * (K0123 + K4)
  let Kker : ℝ := 2 * (K01234 + K5)
  let Kout : ℝ := C242 * Kt * Kker
  have hK102 : 0 ≤ K102 :=
    mul_nonneg (mul_nonneg hC233 hP102) hKinner
  have hK120 : 0 ≤ K120 :=
    mul_nonneg (mul_nonneg hC233 hP120) hKinner
  have hKcore0 : 0 ≤ Kcore0 :=
    mul_nonneg (mul_nonneg hC234 hKouter) hK102
  have hKcore2 : 0 ≤ Kcore2 :=
    mul_nonneg (mul_nonneg hC234 hKouter) hK120
  have hKcore3 : 0 ≤ Kcore3 :=
    mul_nonneg (mul_nonneg hC234 hKouter) hKinner
  have hK0 : 0 ≤ K0 :=
    mul_nonneg (mul_nonneg hC244 hP3201) hKcore0
  have hK1 : 0 ≤ K1 :=
    mul_nonneg (mul_nonneg hC244 hP2301) hKcore0
  have hK2 : 0 ≤ K2 :=
    mul_nonneg (mul_nonneg hC244 hP3102) hKcore2
  have hK3 : 0 ≤ K3 :=
    mul_nonneg (mul_nonneg hC244 hP1302) hKcore3
  have hK4 : 0 ≤ K4 :=
    mul_nonneg (mul_nonneg hC244 hP1203) hKcore3
  have hK5 : 0 ≤ K5 :=
    mul_nonneg (mul_nonneg hC244 hP2103) hKcore2
  have hK01 : 0 ≤ K01 :=
    mul_nonneg (by norm_num) (add_nonneg hK0 hK1)
  have hK012 : 0 ≤ K012 :=
    mul_nonneg (by norm_num) (add_nonneg hK01 hK2)
  have hK0123 : 0 ≤ K0123 :=
    mul_nonneg (by norm_num) (add_nonneg hK012 hK3)
  have hK01234 : 0 ≤ K01234 :=
    mul_nonneg (by norm_num) (add_nonneg hK0123 hK4)
  have hKker : 0 ≤ Kker :=
    mul_nonneg (by norm_num) (add_nonneg hK01234 hK5)
  have hKout : 0 ≤ Kout :=
    mul_nonneg (mul_nonneg hC242 hKt) hKker
  refine ⟨Kout, hKout, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hc :
      H2Poly (I := I) (M := M) g P 1 Kc
        (connectionDifferenceSection (I := I) g₁ g) := by
    refine ⟨hKc, ?_⟩
    simpa only [H2Poly, pow_one] using
      hconn g₁ P hP htie hδ_le hδ0 hδ
  have hinner :
      H2Poly (I := I) (M := M) g P 1 Kinner
        (connectionDifferenceContrInsertionInnerField (I := I) g g₁) := by
    have hs := hp_slot (I := I) (M := M) g P hc
    have hr := hp_reindex (I := I) (M := M) g P
      innerCoreInPerm10 hs
    simpa only [Kinner, fr,
      connectionDifferenceContrInsertionInnerField_eq_reindex_slotExtend] using hr
  have houter :
      H2Poly (I := I) (M := M) g P 1 Kouter
        (connectionDifferenceContravariantInsertionField (I := I) g g₁) := by
    have hs1 := hp_slot (I := I) (M := M) g P hc
    have hs2 := hp_slot (I := I) (M := M) g P hs1
    have hr := hp_reindex (I := I) (M := M) g P
      connectionDifferenceContrInsertionReindexPerm hs2
    simpa only [Kouter, fr, mul_assoc,
      connectionDifferenceContravariantInsertionField_eq_reindex_slotExtend_two] using hr
  have hp102 :
      H2Poly (I := I) (M := M) g P 0 P102
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroOne) := by
    simpa only [P102] using hp_const (I := I) (M := M) g P
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroOne)
  have hp120 :
      H2Poly (I := I) (M := M) g P 0 P120
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationRotateInputs) := by
    simpa only [P120] using hp_const (I := I) (M := M) g P
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationRotateInputs)
  have h102 :
      H2Poly (I := I) (M := M) g P 1 K102
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroOne)
          (connectionDifferenceContrInsertionInnerField (I := I) g g₁)) := by
    simpa only [K102, Nat.zero_add] using
      hp_app_of (I := I) (M := M) g P C233 hC233
        (h233 _ _) hp102 hinner
  have h120 :
      H2Poly (I := I) (M := M) g P 1 K120
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricciQuadraticPermutationRotateInputs)
          (connectionDifferenceContrInsertionInnerField (I := I) g g₁)) := by
    simpa only [K120, Nat.zero_add] using
      hp_app_of (I := I) (M := M) g P C233 hC233
        (h233 _ _) hp120 hinner
  have hcore0 :
      H2Poly (I := I) (M := M) g P 2 Kcore0
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
          (connectionDifferenceContravariantInsertionField (I := I) g g₁)
          (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
            (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroOne)
            (connectionDifferenceContrInsertionInnerField (I := I) g g₁))) := by
    simpa only [Kcore0, Nat.reduceAdd] using
      hp_app_of (I := I) (M := M) g P C234 hC234
        (h234 _ _) houter h102
  have hcore2 :
      H2Poly (I := I) (M := M) g P 2 Kcore2
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
          (connectionDifferenceContravariantInsertionField (I := I) g g₁)
          (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
            (permCoeff (I := I) (M := M) g ricciQuadraticPermutationRotateInputs)
            (connectionDifferenceContrInsertionInnerField (I := I) g g₁))) := by
    simpa only [Kcore2, Nat.reduceAdd] using
      hp_app_of (I := I) (M := M) g P C234 hC234
        (h234 _ _) houter h120
  have hcore3 :
      H2Poly (I := I) (M := M) g P 2 Kcore3
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
          (connectionDifferenceContravariantInsertionField (I := I) g g₁)
          (connectionDifferenceContrInsertionInnerField (I := I) g g₁)) := by
    simpa only [Kcore3, Nat.reduceAdd] using
      hp_app_of (I := I) (M := M) g P C234 hC234
        (h234 _ _) houter hinner
  have hp3201 :
      H2Poly (I := I) (M := M) g P 0 P3201
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeOneTwo) := by
    simpa only [P3201] using hp_const (I := I) (M := M) g P _
  have hp2301 :
      H2Poly (I := I) (M := M) g P 0 P2301
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapBlocks) := by
    simpa only [P2301] using hp_const (I := I) (M := M) g P _
  have hp3102 :
      H2Poly (I := I) (M := M) g P 0 P3102
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeTwo) := by
    simpa only [P3102] using hp_const (I := I) (M := M) g P _
  have hp1302 :
      H2Poly (I := I) (M := M) g P 0 P1302
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneThreeTwo) := by
    simpa only [P1302] using hp_const (I := I) (M := M) g P _
  have hp1203 :
      H2Poly (I := I) (M := M) g P 0 P1203
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneTwo) := by
    simpa only [P1203] using hp_const (I := I) (M := M) g P _
  have hp2103 :
      H2Poly (I := I) (M := M) g P 0 P2103
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroTwo) := by
    simpa only [P2103] using hp_const (I := I) (M := M) g P _
  have h0 :
      H2Poly (I := I) (M := M) g P 2 K0
        (nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo (I := I) (M := M) g g₁) := by
    simpa only [K0, nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo, Nat.zero_add] using
      hp_app_of (I := I) (M := M) g P C244 hC244
        (h244 _ _) hp3201 hcore0
  have h1r :=
    hp_app_of (I := I) (M := M) g P C244 hC244
      (h244 _ _) hp2301 hcore0
  have h1 :
      H2Poly (I := I) (M := M) g P 2 K1
        (reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks (I := I) (M := M) g g₁) := by
    have hr := hp_reindex (I := I) (M := M) g P
      innerCoreInPerm10 h1r
    simpa only [K1, reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks, Nat.zero_add] using hr
  have h2 :
      H2Poly (I := I) (M := M) g P 2 K2
        (nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo (I := I) (M := M) g g₁) := by
    simpa only [K2, nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo, Nat.zero_add] using
      hp_app_of (I := I) (M := M) g P C244 hC244
        (h244 _ _) hp3102 hcore2
  have h3r :=
    hp_app_of (I := I) (M := M) g P C244 hC244
      (h244 _ _) hp1302 hcore3
  have h3 :
      H2Poly (I := I) (M := M) g P 2 K3
        (reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo (I := I) (M := M) g g₁) := by
    have hr := hp_reindex (I := I) (M := M) g P
      innerCoreInPerm10 h3r
    simpa only [K3, reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo, Nat.zero_add] using hr
  have h4 :
      H2Poly (I := I) (M := M) g P 2 K4
        (bareConnectionDifferenceKernelTerm_cycleZeroOneTwo (I := I) (M := M) g g₁) := by
    simpa only [K4, bareConnectionDifferenceKernelTerm_cycleZeroOneTwo, Nat.zero_add] using
      hp_app_of (I := I) (M := M) g P C244 hC244
        (h244 _ _) hp1203 hcore3
  have h5r :=
    hp_app_of (I := I) (M := M) g P C244 hC244
      (h244 _ _) hp2103 hcore2
  have h5 :
      H2Poly (I := I) (M := M) g P 2 K5
        (reindexedNestedConnectionDifferenceKernelTerm_rotateInputs_swapZeroTwo (I := I) (M := M) g g₁) := by
    have hr := hp_reindex (I := I) (M := M) g P
      innerCoreInPerm10 h5r
    simpa only [K5, reindexedNestedConnectionDifferenceKernelTerm_rotateInputs_swapZeroTwo, Nat.zero_add] using hr
  have h01 :
      H2Poly (I := I) (M := M) g P 2 K01
        (nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo (I := I) (M := M) g g₁ +
          reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks (I := I) (M := M) g g₁) := by
    simpa only [K01] using hp_add (I := I) (M := M) g P h0 h1
  have h012 :
      H2Poly (I := I) (M := M) g P 2 K012
        (nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo (I := I) (M := M) g g₁ +
          reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks (I := I) (M := M) g g₁ +
          nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo (I := I) (M := M) g g₁) := by
    simpa only [K012] using hp_add (I := I) (M := M) g P h01 h2
  have h0123 :
      H2Poly (I := I) (M := M) g P 2 K0123
        (nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo (I := I) (M := M) g g₁ +
          reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks (I := I) (M := M) g g₁ +
          nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo (I := I) (M := M) g g₁ +
          reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo (I := I) (M := M) g g₁) := by
    simpa only [K0123] using hp_add (I := I) (M := M) g P h012 h3
  have h01234 :
      H2Poly (I := I) (M := M) g P 2 K01234
        (nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo (I := I) (M := M) g g₁ +
          reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks (I := I) (M := M) g g₁ +
          nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo (I := I) (M := M) g g₁ +
          reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo (I := I) (M := M) g g₁ +
          bareConnectionDifferenceKernelTerm_cycleZeroOneTwo (I := I) (M := M) g g₁) := by
    simpa only [K01234] using hp_add (I := I) (M := M) g P h0123 h4
  have hk :
      H2Poly (I := I) (M := M) g P 2 Kker
        (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g g₁) := by
    have hsum := hp_add (I := I) (M := M) g P h01234 h5
    rw [← ricciConnectionDifferenceQuadraticKernel_eq_sum (I := I) (M := M) g g₁] at hsum
    simpa only [Kker] using hsum
  have ht :
      H2Poly (I := I) (M := M) g P 1 Kt
        (ricciCometricFourTraceCastG0 (I := I) g g₁) := by
    refine ⟨hKt, ?_⟩
    have hraw := htrace g₁ P hP htie hδ_le hδ0 hδ
    have h23 := covariantJetNormSq_mono (I := I) (M := M) g
      (by omega : 2 ≤ 3) P
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciCometricFourTraceCastG0 (I := I) g g₁) ≤
        Kt * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := hraw
      _ ≤ Kt * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) :=
        mul_le_mul_of_nonneg_left (by linarith) hKt
      _ = Kt * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 1 := by
        rw [pow_one]
  have hout :=
    hp_app_of (I := I) (M := M) g P C242 hC242
      (h242 _ _) ht hk
  simpa only [Kout, ricciConnectionDifferenceQuadraticArm, Nat.reduceAdd] using hout.2

private theorem aa_h2_of
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (Q Qt : ℝ),
        0 ≤ Q → 0 ≤ Qt →
        covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceSection (I := I) g₁ g) ≤ Q →
        covariantJetNormSq (I := I) (M := M) g 2
            (ricciCometricFourTraceCastG0 (I := I) g g₁) ≤ Qt →
        covariantJetNormSq (I := I) (M := M) g 2
            (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g g₁) ≤
          C * Qt * Q ^ 2 := by
  classical
  obtain ⟨C233, hC233, h233⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 3 3
  obtain ⟨C234, hC234, h234⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 3 4
  obtain ⟨C244, hC244, h244⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 4 4
  obtain ⟨C242, hC242, h242⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 4 2
  let fr : ℝ := Module.finrank ℝ E
  let P102 : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroOne)
  let P120 : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationRotateInputs)
  let P3201 : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeOneTwo)
  let P2301 : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapBlocks)
  let P3102 : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeTwo)
  let P1302 : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneThreeTwo)
  let P1203 : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneTwo)
  let P2103 : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroTwo)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hP102 : 0 ≤ P102 :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hP120 : 0 ≤ P120 :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hP3201 : 0 ≤ P3201 :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hP2301 : 0 ≤ P2301 :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hP3102 : 0 ≤ P3102 :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hP1302 : 0 ≤ P1302 :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hP1203 : 0 ≤ P1203 :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hP2103 : 0 ≤ P2103 :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  let D102 : ℝ := C233 * P102 * fr
  let D120 : ℝ := C233 * P120 * fr
  let Dcore0 : ℝ := C234 * (fr * fr) * D102
  let Dcore2 : ℝ := C234 * (fr * fr) * D120
  let Dcore3 : ℝ := C234 * (fr * fr) * fr
  let D0 : ℝ := C244 * P3201 * Dcore0
  let D1 : ℝ := C244 * P2301 * Dcore0
  let D2 : ℝ := C244 * P3102 * Dcore2
  let D3 : ℝ := C244 * P1302 * Dcore3
  let D4 : ℝ := C244 * P1203 * Dcore3
  let D5 : ℝ := C244 * P2103 * Dcore2
  let D01 : ℝ := 2 * (D0 + D1)
  let D012 : ℝ := 2 * (D01 + D2)
  let D0123 : ℝ := 2 * (D012 + D3)
  let D01234 : ℝ := 2 * (D0123 + D4)
  let Dker : ℝ := 2 * (D01234 + D5)
  let C : ℝ := C242 * Dker
  have hD102 : 0 ≤ D102 :=
    mul_nonneg (mul_nonneg hC233 hP102) hfr
  have hD120 : 0 ≤ D120 :=
    mul_nonneg (mul_nonneg hC233 hP120) hfr
  have hDcore0 : 0 ≤ Dcore0 :=
    mul_nonneg (mul_nonneg hC234 (mul_nonneg hfr hfr)) hD102
  have hDcore2 : 0 ≤ Dcore2 :=
    mul_nonneg (mul_nonneg hC234 (mul_nonneg hfr hfr)) hD120
  have hDcore3 : 0 ≤ Dcore3 :=
    mul_nonneg (mul_nonneg hC234 (mul_nonneg hfr hfr)) hfr
  have hD0 : 0 ≤ D0 :=
    mul_nonneg (mul_nonneg hC244 hP3201) hDcore0
  have hD1 : 0 ≤ D1 :=
    mul_nonneg (mul_nonneg hC244 hP2301) hDcore0
  have hD2 : 0 ≤ D2 :=
    mul_nonneg (mul_nonneg hC244 hP3102) hDcore2
  have hD3 : 0 ≤ D3 :=
    mul_nonneg (mul_nonneg hC244 hP1302) hDcore3
  have hD4 : 0 ≤ D4 :=
    mul_nonneg (mul_nonneg hC244 hP1203) hDcore3
  have hD5 : 0 ≤ D5 :=
    mul_nonneg (mul_nonneg hC244 hP2103) hDcore2
  have hD01 : 0 ≤ D01 :=
    mul_nonneg (by norm_num) (add_nonneg hD0 hD1)
  have hD012 : 0 ≤ D012 :=
    mul_nonneg (by norm_num) (add_nonneg hD01 hD2)
  have hD0123 : 0 ≤ D0123 :=
    mul_nonneg (by norm_num) (add_nonneg hD012 hD3)
  have hD01234 : 0 ≤ D01234 :=
    mul_nonneg (by norm_num) (add_nonneg hD0123 hD4)
  have hDker : 0 ≤ Dker :=
    mul_nonneg (by norm_num) (add_nonneg hD01234 hD5)
  have hC : 0 ≤ C := mul_nonneg hC242 hDker
  refine ⟨C, hC, ?_⟩
  intro g₁ Q Qt hQ hQt hconn htrace
  let Z : SmoothCcTensor g 0 2 := 0
  have hc :
      H2Poly (I := I) (M := M) g Z 0 Q
        (connectionDifferenceSection (I := I) g₁ g) := by
    simpa only [H2Poly, pow_zero, mul_one] using And.intro hQ hconn
  have hinner :
      H2Poly (I := I) (M := M) g Z 0 (fr * Q)
        (connectionDifferenceContrInsertionInnerField (I := I) g g₁) := by
    have hs := hp_slot (I := I) (M := M) g Z hc
    have hr := hp_reindex (I := I) (M := M) g Z
      innerCoreInPerm10 hs
    simpa only [fr,
      connectionDifferenceContrInsertionInnerField_eq_reindex_slotExtend] using hr
  have houter :
      H2Poly (I := I) (M := M) g Z 0 (fr * (fr * Q))
        (connectionDifferenceContravariantInsertionField (I := I) g g₁) := by
    have hs1 := hp_slot (I := I) (M := M) g Z hc
    have hs2 := hp_slot (I := I) (M := M) g Z hs1
    have hr := hp_reindex (I := I) (M := M) g Z
      connectionDifferenceContrInsertionReindexPerm hs2
    simpa only [fr,
      connectionDifferenceContravariantInsertionField_eq_reindex_slotExtend_two] using hr
  have hp102 :
      H2Poly (I := I) (M := M) g Z 0 P102
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroOne) := by
    simpa only [P102] using hp_const (I := I) (M := M) g Z _
  have hp120 :
      H2Poly (I := I) (M := M) g Z 0 P120
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationRotateInputs) := by
    simpa only [P120] using hp_const (I := I) (M := M) g Z _
  have h102 :
      H2Poly (I := I) (M := M) g Z 0 (D102 * Q)
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroOne)
          (connectionDifferenceContrInsertionInnerField (I := I) g g₁)) := by
    have hraw := hp_app_of (I := I) (M := M) g Z C233 hC233
      (h233 _ _) hp102 hinner
    convert hraw using 1;
      simp only [D102]; ring
  have h120 :
      H2Poly (I := I) (M := M) g Z 0 (D120 * Q)
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricciQuadraticPermutationRotateInputs)
          (connectionDifferenceContrInsertionInnerField (I := I) g g₁)) := by
    have hraw := hp_app_of (I := I) (M := M) g Z C233 hC233
      (h233 _ _) hp120 hinner
    convert hraw using 1;
      simp only [D120]; ring
  have hcore0 :
      H2Poly (I := I) (M := M) g Z 0 (Dcore0 * Q ^ 2)
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
          (connectionDifferenceContravariantInsertionField (I := I) g g₁)
          (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
            (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroOne)
            (connectionDifferenceContrInsertionInnerField (I := I) g g₁))) := by
    have hraw := hp_app_of (I := I) (M := M) g Z C234 hC234
      (h234 _ _) houter h102
    convert hraw using 1;
      simp only [Dcore0, D102]; ring
  have hcore2 :
      H2Poly (I := I) (M := M) g Z 0 (Dcore2 * Q ^ 2)
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
          (connectionDifferenceContravariantInsertionField (I := I) g g₁)
          (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
            (permCoeff (I := I) (M := M) g ricciQuadraticPermutationRotateInputs)
            (connectionDifferenceContrInsertionInnerField (I := I) g g₁))) := by
    have hraw := hp_app_of (I := I) (M := M) g Z C234 hC234
      (h234 _ _) houter h120
    convert hraw using 1;
      simp only [Dcore2, D120]; ring
  have hcore3 :
      H2Poly (I := I) (M := M) g Z 0 (Dcore3 * Q ^ 2)
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
          (connectionDifferenceContravariantInsertionField (I := I) g g₁)
          (connectionDifferenceContrInsertionInnerField (I := I) g g₁)) := by
    have hraw := hp_app_of (I := I) (M := M) g Z C234 hC234
      (h234 _ _) houter hinner
    convert hraw using 1;
      simp only [Dcore3]; ring
  have hp3201 :
      H2Poly (I := I) (M := M) g Z 0 P3201
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeOneTwo) := by
    simpa only [P3201] using hp_const (I := I) (M := M) g Z _
  have hp2301 :
      H2Poly (I := I) (M := M) g Z 0 P2301
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapBlocks) := by
    simpa only [P2301] using hp_const (I := I) (M := M) g Z _
  have hp3102 :
      H2Poly (I := I) (M := M) g Z 0 P3102
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeTwo) := by
    simpa only [P3102] using hp_const (I := I) (M := M) g Z _
  have hp1302 :
      H2Poly (I := I) (M := M) g Z 0 P1302
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneThreeTwo) := by
    simpa only [P1302] using hp_const (I := I) (M := M) g Z _
  have hp1203 :
      H2Poly (I := I) (M := M) g Z 0 P1203
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneTwo) := by
    simpa only [P1203] using hp_const (I := I) (M := M) g Z _
  have hp2103 :
      H2Poly (I := I) (M := M) g Z 0 P2103
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroTwo) := by
    simpa only [P2103] using hp_const (I := I) (M := M) g Z _
  have h0 :
      H2Poly (I := I) (M := M) g Z 0 (D0 * Q ^ 2)
        (nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo (I := I) (M := M) g g₁) := by
    unfold nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo
    have hraw := hp_app_of (I := I) (M := M) g Z C244 hC244
      (h244 _ _) hp3201 hcore0
    convert hraw using 1;
      simp only [D0]; ring
  have h1r := hp_app_of (I := I) (M := M) g Z C244 hC244
    (h244 _ _) hp2301 hcore0
  have h1 :
      H2Poly (I := I) (M := M) g Z 0 (D1 * Q ^ 2)
        (reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks (I := I) (M := M) g g₁) := by
    unfold reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks
    have hr := hp_reindex (I := I) (M := M) g Z
      innerCoreInPerm10 h1r
    convert hr using 1;
      simp only [D1]; ring
  have h2 :
      H2Poly (I := I) (M := M) g Z 0 (D2 * Q ^ 2)
        (nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo (I := I) (M := M) g g₁) := by
    unfold nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo
    have hraw := hp_app_of (I := I) (M := M) g Z C244 hC244
      (h244 _ _) hp3102 hcore2
    convert hraw using 1;
      simp only [D2]; ring
  have h3r := hp_app_of (I := I) (M := M) g Z C244 hC244
    (h244 _ _) hp1302 hcore3
  have h3 :
      H2Poly (I := I) (M := M) g Z 0 (D3 * Q ^ 2)
        (reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo (I := I) (M := M) g g₁) := by
    unfold reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo
    have hr := hp_reindex (I := I) (M := M) g Z
      innerCoreInPerm10 h3r
    convert hr using 1;
      simp only [D3]; ring
  have h4 :
      H2Poly (I := I) (M := M) g Z 0 (D4 * Q ^ 2)
        (bareConnectionDifferenceKernelTerm_cycleZeroOneTwo (I := I) (M := M) g g₁) := by
    unfold bareConnectionDifferenceKernelTerm_cycleZeroOneTwo
    have hraw := hp_app_of (I := I) (M := M) g Z C244 hC244
      (h244 _ _) hp1203 hcore3
    convert hraw using 1;
      simp only [D4]; ring
  have h5r := hp_app_of (I := I) (M := M) g Z C244 hC244
    (h244 _ _) hp2103 hcore2
  have h5 :
      H2Poly (I := I) (M := M) g Z 0 (D5 * Q ^ 2)
        (reindexedNestedConnectionDifferenceKernelTerm_rotateInputs_swapZeroTwo (I := I) (M := M) g g₁) := by
    unfold reindexedNestedConnectionDifferenceKernelTerm_rotateInputs_swapZeroTwo
    have hr := hp_reindex (I := I) (M := M) g Z
      innerCoreInPerm10 h5r
    convert hr using 1;
      simp only [D5]; ring
  have h01 :
      H2Poly (I := I) (M := M) g Z 0 (D01 * Q ^ 2)
        (nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo (I := I) (M := M) g g₁ +
          reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks (I := I) (M := M) g g₁) := by
    have hraw := hp_add (I := I) (M := M) g Z h0 h1
    convert hraw using 1;
      simp only [D01]; ring
  have h012 :
      H2Poly (I := I) (M := M) g Z 0 (D012 * Q ^ 2)
        (nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo (I := I) (M := M) g g₁ +
          reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks (I := I) (M := M) g g₁ +
          nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo (I := I) (M := M) g g₁) := by
    have hraw := hp_add (I := I) (M := M) g Z h01 h2
    convert hraw using 1;
      simp only [D012]; ring
  have h0123 :
      H2Poly (I := I) (M := M) g Z 0 (D0123 * Q ^ 2)
        (nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo (I := I) (M := M) g g₁ +
          reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks (I := I) (M := M) g g₁ +
          nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo (I := I) (M := M) g g₁ +
          reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo (I := I) (M := M) g g₁) := by
    have hraw := hp_add (I := I) (M := M) g Z h012 h3
    convert hraw using 1;
      simp only [D0123]; ring
  have h01234 :
      H2Poly (I := I) (M := M) g Z 0 (D01234 * Q ^ 2)
        (nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo (I := I) (M := M) g g₁ +
          reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks (I := I) (M := M) g g₁ +
          nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo (I := I) (M := M) g g₁ +
          reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo (I := I) (M := M) g g₁ +
          bareConnectionDifferenceKernelTerm_cycleZeroOneTwo (I := I) (M := M) g g₁) := by
    have hraw := hp_add (I := I) (M := M) g Z h0123 h4
    convert hraw using 1;
      simp only [D01234]; ring
  have hk :
      H2Poly (I := I) (M := M) g Z 0 (Dker * Q ^ 2)
        (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g g₁) := by
    have hraw := hp_add (I := I) (M := M) g Z h01234 h5
    rw [← ricciConnectionDifferenceQuadraticKernel_eq_sum (I := I) (M := M) g g₁] at hraw
    convert hraw using 1;
      simp only [Dker]; ring
  have ht :
      H2Poly (I := I) (M := M) g Z 0 Qt
        (ricciCometricFourTraceCastG0 (I := I) g g₁) := by
    simpa only [H2Poly, pow_zero, mul_one] using And.intro hQt htrace
  have hout := hp_app_of (I := I) (M := M) g Z C242 hC242
    (h242 _ _) ht hk
  have hout' :
      H2Poly (I := I) (M := M) g Z 0 (C * Qt * Q ^ 2)
        (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g g₁) := by
    unfold ricciConnectionDifferenceQuadraticArm
    convert hout using 1;
      simp only [C]; ring
  simpa only [pow_zero, mul_one] using hout'.2

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem grad_l2_sq
    (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (S : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r (s + 1) i
        (covGrad (I := I) (M := M) g r s S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s (i + 1) S‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs
    (I := I) (M := M) g r s i S x

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem grad_h2_le_h3
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g 2
        (covGrad (I := I) (M := M) g r s S) ≤
      covariantJetNormSq (I := I) (M := M) g 3 S := by
  have h0 := grad_l2_sq (I := I) (M := M) g r s 0 S
  have h1 := grad_l2_sq (I := I) (M := M) g r s 1 S
  have h2 := grad_l2_sq (I := I) (M := M) g r s 2 S
  unfold covariantJetNormSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 h2 ⊢
  rw [h0, h1, h2]
  nlinarith only [sq_nonneg ‖S‖]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem jet3_le_grad2
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g 3 S ≤
      covariantJetNormSq (I := I) (M := M) g 2 S +
        covariantJetNormSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g r s S) := by
  have h0 := grad_l2_sq (I := I) (M := M) g r s 0 S
  have h1 := grad_l2_sq (I := I) (M := M) g r s 1 S
  have h2 := grad_l2_sq (I := I) (M := M) g r s 2 S
  unfold covariantJetNormSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 h2 ⊢
  rw [h0, h1, h2]
  nlinarith only [sq_nonneg
    ‖iteratedCovGrad (I := I) g r s 1 S‖,
    sq_nonneg ‖iteratedCovGrad (I := I) g r s 2 S‖]

private theorem app_h3_mul
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        covariantJetNormSq (I := I) (M := M) g 3
            (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
          C * covariantJetNormSq (I := I) (M := M) g 3 Φ *
            covariantJetNormSq (I := I) (M := M) g 3 W := by
  obtain ⟨C0, hC0, h0⟩ :=
    app_h2_mul (I := I) (M := M) hDim g p r c
  obtain ⟨C1, hC1, h1⟩ :=
    app_h2_mul (I := I) (M := M) hDim g p r (c + 1)
  obtain ⟨C2, hC2, h2⟩ :=
    app_h2_mul (I := I) (M := M) hDim g p (r + 1) (c + 1)
  let fr : ℝ := Module.finrank ℝ E
  let C : ℝ := C0 + 2 * (C1 + C2 * fr)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg hC0
      (mul_nonneg (by norm_num) (add_nonneg hC1 (mul_nonneg hC2 hfr)))
  refine ⟨C, hC, ?_⟩
  intro Φ W
  let Y : SmoothCcTensor g p c :=
    ccOperatorFieldComp (I := I) (M := M) g p r c Φ W
  let A : SmoothCcTensor g p (c + 1) :=
    ccOperatorFieldComp (I := I) (M := M) g p r (c + 1)
      (covGrad (I := I) (M := M) g r c Φ) W
  let B : SmoothCcTensor g p (c + 1) :=
    ccOperatorFieldComp (I := I) (M := M) g p (r + 1) (c + 1)
      (slotExtend (I := I) (M := M) g r c Φ)
      (covGrad (I := I) (M := M) g p r W)
  have hΦ23 := covariantJetNormSq_mono (I := I) (M := M) g
    (by omega : 2 ≤ 3) Φ
  have hW23 := covariantJetNormSq_mono (I := I) (M := M) g
    (by omega : 2 ≤ 3) W
  have hΦ0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g Φ
  have hW0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g W
  have hΦ30 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g Φ
  have hW30 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g W
  have hY2 :
      covariantJetNormSq (I := I) (M := M) g 2 Y ≤
        C0 * covariantJetNormSq (I := I) (M := M) g 3 Φ *
          covariantJetNormSq (I := I) (M := M) g 3 W := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 Y ≤
          C0 * covariantJetNormSq (I := I) (M := M) g 2 Φ *
            covariantJetNormSq (I := I) (M := M) g 2 W := by
        simpa only [Y] using h0 Φ W
      _ ≤ C0 * covariantJetNormSq (I := I) (M := M) g 3 Φ *
            covariantJetNormSq (I := I) (M := M) g 2 W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hΦ23 hC0) hW0
      _ ≤ C0 * covariantJetNormSq (I := I) (M := M) g 3 Φ *
            covariantJetNormSq (I := I) (M := M) g 3 W := by
        exact mul_le_mul_of_nonneg_left hW23 (mul_nonneg hC0 hΦ30)
  have hA2 :
      covariantJetNormSq (I := I) (M := M) g 2 A ≤
        C1 * covariantJetNormSq (I := I) (M := M) g 3 Φ *
          covariantJetNormSq (I := I) (M := M) g 3 W := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 A ≤
          C1 * covariantJetNormSq (I := I) (M := M) g 2
              (covGrad (I := I) (M := M) g r c Φ) *
            covariantJetNormSq (I := I) (M := M) g 2 W := by
        simpa only [A] using
          h1 (covGrad (I := I) (M := M) g r c Φ) W
      _ ≤ C1 * covariantJetNormSq (I := I) (M := M) g 3 Φ *
            covariantJetNormSq (I := I) (M := M) g 2 W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (grad_h2_le_h3 (I := I) (M := M) g Φ) hC1) hW0
      _ ≤ C1 * covariantJetNormSq (I := I) (M := M) g 3 Φ *
            covariantJetNormSq (I := I) (M := M) g 3 W := by
        exact mul_le_mul_of_nonneg_left hW23 (mul_nonneg hC1 hΦ30)
  have hB2 :
      covariantJetNormSq (I := I) (M := M) g 2 B ≤
        (C2 * fr) * covariantJetNormSq (I := I) (M := M) g 3 Φ *
          covariantJetNormSq (I := I) (M := M) g 3 W := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 B ≤
          C2 * covariantJetNormSq (I := I) (M := M) g 2
              (slotExtend (I := I) (M := M) g r c Φ) *
            covariantJetNormSq (I := I) (M := M) g 2
              (covGrad (I := I) (M := M) g p r W) := by
        simpa only [B] using
          h2 (slotExtend (I := I) (M := M) g r c Φ)
            (covGrad (I := I) (M := M) g p r W)
      _ ≤ C2 * (fr * covariantJetNormSq (I := I) (M := M) g 2 Φ) *
            covariantJetNormSq (I := I) (M := M) g 2
              (covGrad (I := I) (M := M) g p r W) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (by simpa only [fr] using
              slot_h2 (I := I) (M := M) g r c Φ) hC2)
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
            (covGrad (I := I) (M := M) g p r W))
      _ ≤ C2 * (fr * covariantJetNormSq (I := I) (M := M) g 2 Φ) *
            covariantJetNormSq (I := I) (M := M) g 3 W := by
        exact mul_le_mul_of_nonneg_left
          (grad_h2_le_h3 (I := I) (M := M) g W)
          (mul_nonneg hC2 (mul_nonneg hfr hΦ0))
      _ ≤ C2 * (fr * covariantJetNormSq (I := I) (M := M) g 3 Φ) *
            covariantJetNormSq (I := I) (M := M) g 3 W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hΦ23 hfr) hC2) hW30
      _ = (C2 * fr) * covariantJetNormSq (I := I) (M := M) g 3 Φ *
            covariantJetNormSq (I := I) (M := M) g 3 W := by ring
  have hgrad :
      covariantJetNormSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g p c Y) ≤
        2 * (C1 + C2 * fr) *
          covariantJetNormSq (I := I) (M := M) g 3 Φ *
          covariantJetNormSq (I := I) (M := M) g 3 W := by
    rw [show covGrad (I := I) (M := M) g p c Y = A + B by
      simpa only [Y, A, B] using
        covGrad_operatorFieldComposition_eq (I := I) (M := M) g p r c Φ W]
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (A + B) ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 2 A +
            covariantJetNormSq (I := I) (M := M) g 2 B) :=
        covariantJetNormSq_add_le (I := I) (M := M) g 2 A B
      _ ≤ 2 * (C1 * covariantJetNormSq (I := I) (M := M) g 3 Φ *
              covariantJetNormSq (I := I) (M := M) g 3 W +
            (C2 * fr) * covariantJetNormSq (I := I) (M := M) g 3 Φ *
              covariantJetNormSq (I := I) (M := M) g 3 W) :=
        mul_le_mul_of_nonneg_left (add_le_add hA2 hB2) (by norm_num)
      _ = 2 * (C1 + C2 * fr) *
          covariantJetNormSq (I := I) (M := M) g 3 Φ *
          covariantJetNormSq (I := I) (M := M) g 3 W := by ring
  calc
    covariantJetNormSq (I := I) (M := M) g 3
        (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) =
      covariantJetNormSq (I := I) (M := M) g 3 Y := rfl
    _ ≤ covariantJetNormSq (I := I) (M := M) g 2 Y +
        covariantJetNormSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g p c Y) :=
      jet3_le_grad2 (I := I) (M := M) g Y
    _ ≤ C0 * covariantJetNormSq (I := I) (M := M) g 3 Φ *
          covariantJetNormSq (I := I) (M := M) g 3 W +
        2 * (C1 + C2 * fr) *
          covariantJetNormSq (I := I) (M := M) g 3 Φ *
          covariantJetNormSq (I := I) (M := M) g 3 W :=
      add_le_add hY2 hgrad
    _ = C * covariantJetNormSq (I := I) (M := M) g 3 Φ *
          covariantJetNormSq (I := I) (M := M) g 3 W := by
      simp only [C]
      ring

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem sharp_eq_slot0
    (g g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g g₁ =
      slotInsertEndoCc (I := I) (M := M) g 0
        (metricComparisonEndomorphismField (I := I) (M := M) g g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (slotInsertEndoCc (I := I) (M := M) g 0
          (metricComparisonEndomorphismField (I := I) (M := M) g g₁)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (metricComparisonEndomorphism (I := I) g g₁ x) om from rfl]
  rw [cotangentToDual_slotInsertEndoFib' (I := I) (M := M) x
    (metricComparisonEndomorphism (I := I) g g₁ x) om w]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g g₁).toSection x) om =
      g0FlatCLM (I := I) g x (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [cotangentToDual_g0FlatCLM]
  rw [show cotangentToDual (I := I) om
      (metricComparisonEndomorphism (I := I) g g₁ x w) =
      g₁.inner x (inverseMetricSharpFib (I := I) g₁ x om)
        (metricComparisonEndomorphism (I := I) g g₁ x w) from by
    rw [← cotangentToDualLinear_apply]
    exact (inverseMetricSharpFib_inner (I := I) g₁ x om
      (metricComparisonEndomorphism (I := I) g g₁ x w)).symm]
  rw [show metricComparisonEndomorphism (I := I) g g₁ x w =
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g x w) from by
    rw [metricComparisonEndomorphism_apply]]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om)
    (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g x w))]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x
    (g0FlatCLM (I := I) g x w) (inverseMetricSharpFib (I := I) g₁ x om)]
  rw [cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  rw [g.symm x w (inverseMetricSharpFib (I := I) g₁ x om)]

private theorem sharp_h3_rf
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 3
          (sharpFlatEndoCc (I := I) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) := by
  classical
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀0 : 0 ≤ Λ₀ :=
    mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨Λ, Flow, hΛ, hFlow0, hFlow⟩ :=
    sharpFlatEndoCc_lowOrder_jetL2_radiusFree
      (I := I) (M := M) g
        (2 * Module.finrank ℝ E + 10) hδ₀ hΛ₀0
  refine ⟨Flow 3, hFlow0 3, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symm_eq_self (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2 := by
    intro x
    rw [← hsymm]
    exact riemannianFiberNormSq_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  simpa only [covariantJetNormSq, Nat.reduceAdd] using
    (hFlow g₁ P htie hδ_le hδ0 hδ hsup).2 3 (by omega)

private theorem endo_slot_l2
    (g : SmoothRiemannianMetric I M) (s i : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) ^ s *
    riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
      ((iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g 1 (1 + i)
      (iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ))).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (s + 1) ((s + 1) + i)
    (iteratedCovGrad (I := I) g (s + 1) (s + 1) i
      (slotInsertEndoCc (I := I) (M := M) g s Λ))
    F hF (fun x =>
      riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo
        (I := I) (M := M) g s Λ i x)
  have hint :
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
          ((iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

private theorem endo_slot_h3
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    covariantJetNormSq (I := I) (M := M) g 3
        (slotInsertEndoCc (I := I) (M := M) g s Λ) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        covariantJetNormSq (I := I) (M := M) g 3
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by
  unfold covariantJetNormSq
  calc
    ∑ i ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 4, (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        endo_slot_l2 (I := I) (M := M) g s i Λ
    _ = (Module.finrank ℝ E : ℝ) ^ s *
        ∑ i ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem sharp_h2_low
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (sharpFlatEndoCc (I := I) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  classical
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀0 : 0 ≤ Λ₀ :=
    mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨Λ, Flow, hΛ, hFlow0, hFlow⟩ :=
    sharpFlatEndoCc_lowOrder_jetL2_radiusFree
      (I := I) (M := M) g
        (2 * Module.finrank ℝ E + 10) hδ₀ hΛ₀0
  refine ⟨Flow 2, hFlow0 2, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symm_eq_self (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2 := by
    intro x
    rw [← hsymm]
    exact riemannianFiberNormSq_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  simpa only [covariantJetNormSq, Nat.reduceAdd] using
    (hFlow g₁ P htie hδ_le hδ0 hδ hsup).2 2 (by omega)

private theorem endo_slot_h2
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    covariantJetNormSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g s Λ) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by
  unfold covariantJetNormSq
  calc
    ∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 3, (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        endo_slot_l2 (I := I) (M := M) g s i Λ
    _ = (Module.finrank ℝ E : ℝ) ^ s *
        ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem full_slot_h2_low
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g s
            (metricComparisonEndomorphismField (I := I) (M := M) g g₁)) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  obtain ⟨K₀, hK₀, hsharp⟩ :=
    sharp_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := fr ^ s * K₀
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K := mul_nonneg (pow_nonneg hfr s) hK₀
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g s
          (metricComparisonEndomorphismField (I := I) (M := M) g g₁)) ≤
      fr ^ s * covariantJetNormSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g 0
          (metricComparisonEndomorphismField (I := I) (M := M) g g₁)) := by
      simpa only [fr] using endo_slot_h2 (I := I) (M := M) g s
        (metricComparisonEndomorphismField (I := I) (M := M) g g₁)
    _ = fr ^ s * covariantJetNormSq (I := I) (M := M) g 2
        (sharpFlatEndoCc (I := I) g g₁) := by
      rw [sharp_eq_slot0 (I := I) (M := M) g g₁]
    _ ≤ fr ^ s * (K₀ *
        (1 + covariantJetNormSq (I := I) (M := M) g 2 P)) :=
      mul_le_mul_of_nonneg_left
        (hsharp g₁ P hP htie hδ_le hδ0 hδ) (pow_nonneg hfr s)
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
      simp only [K]
      ring

private theorem connLow_h2_low
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceLowOrderOperator (I := I) (M := M) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  obtain ⟨Ks, hKs, hslot⟩ :=
    full_slot_h2_low (I := I) (M := M) g 2 hδ₀0 hδ₀
  obtain ⟨C, hC, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 3 3 3
  let Kk : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (koszulOp (I := I) (M := M) g)
  let Kp : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g connectionDifferenceLowOrderPermutation)
  let Ki : ℝ := C * Ks * Kk
  let K : ℝ := C * Kp * Ki
  have hKk : 0 ≤ Kk := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hKp : 0 ≤ Kp := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hKi : 0 ≤ Ki := mul_nonneg (mul_nonneg hC hKs) hKk
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hC hKp) hKi
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hs :
      H2Poly (I := I) (M := M) g P 0
        (Ks * (1 + covariantJetNormSq (I := I) (M := M) g 2 P))
        (slotInsertEndoCc (I := I) (M := M) g 2
          (metricComparisonEndomorphismField (I := I) (M := M) g g₁)) := by
    refine ⟨mul_nonneg hKs (by
      linarith [covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g P]), ?_⟩
    simpa only [H2Poly, pow_zero, mul_one] using
      hslot g₁ P hP htie hδ_le hδ0 hδ
  have hk :
      H2Poly (I := I) (M := M) g P 0 Kk
        (koszulOp (I := I) (M := M) g) := by
    simpa only [Kk] using hp_const (I := I) (M := M) g P
      (koszulOp (I := I) (M := M) g)
  have hi := hp_app_of (I := I) (M := M) g P C hC
    (happ _ _) hs hk
  have hp :
      H2Poly (I := I) (M := M) g P 0 Kp
        (permCoeff (I := I) (M := M) g connectionDifferenceLowOrderPermutation) := by
    simpa only [Kp] using hp_const (I := I) (M := M) g P
      (permCoeff (I := I) (M := M) g connectionDifferenceLowOrderPermutation)
  have hout := hp_app_of (I := I) (M := M) g P C hC
    (happ _ _) hp hi
  rw [connectionDifferenceLowOrderOperator]
  calc
    _ ≤ C * (Kp * (C *
        (Ks * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) * Kk))) := by
      simpa only [H2Poly, pow_zero, mul_one, Nat.zero_add, mul_assoc]
        using hout.2
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
      simp only [K, Ki]
      ring

private theorem connLower_h2_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifferenceCoefficient (I := I) g g₁) ≤
        (B R * A) ^ 2 := by
  obtain ⟨K, hK, hconn⟩ :=
    connLow_h2_low (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨C, hC, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 3 3
  let B : ℝ → ℝ := fun R => Real.sqrt (C * K * (1 + R ^ 2))
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R :=
    fun R _ => Real.sqrt_nonneg _
  refine ⟨B, hB, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ R A hR hA hP2 hP3
  have hcoeff :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceLowOrderOperator (I := I) (M := M) g g₁) ≤
        K * (1 + R ^ 2) := by
    exact (hconn g₁ P hP htie hδ_le hδ0 hδ).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hP2) hK)
  have hgrad :
      covariantJetNormSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g 0 2 P) ≤ A ^ 2 :=
    (grad_h2_le_h3 (I := I) (M := M) g P).trans hP3
  have hraw := happ
    (connectionDifferenceLowOrderOperator (I := I) (M := M) g g₁)
    (covGrad (I := I) (M := M) g 0 2 P)
  have hCKR : 0 ≤ C * K * (1 + R ^ 2) :=
    mul_nonneg (mul_nonneg hC hK) (by positivity)
  have hprod :
      C * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceLowOrderOperator (I := I) (M := M) g g₁) *
          covariantJetNormSq (I := I) (M := M) g 2
            (covGrad (I := I) (M := M) g 0 2 P) ≤
        (C * K * (1 + R ^ 2)) * A ^ 2 := by
    exact mul_le_mul
      (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hcoeff hC) hgrad
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
        (covGrad (I := I) (M := M) g 0 2 P))
      (mul_nonneg (mul_nonneg hC hK) (by positivity))
  rw [← connLowOp_app (I := I) (M := M) g g₁ P hP htie]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g 0 3 3
          (connectionDifferenceLowOrderOperator (I := I) (M := M) g g₁)
          (covGrad (I := I) (M := M) g 0 2 P)) ≤
      C * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceLowOrderOperator (I := I) (M := M) g g₁) *
        covariantJetNormSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g 0 2 P) := hraw
    _ ≤ (C * K * (1 + R ^ 2)) * A ^ 2 := hprod
    _ = (B R * A) ^ 2 := by
      rw [mul_pow, show (B R) ^ 2 = C * K * (1 + R ^ 2) by
        simpa only [B] using Real.sq_sqrt hCKR]

private theorem conn_h2_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) g₁ g) ≤
        (B R * A) ^ 2 := by
  obtain ⟨B, hB, hlower⟩ :=
    connLower_h2_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  refine ⟨B, hB, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ R A hR hA hP2 hP3
  have heq :
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifferenceCoefficient (I := I) g g₁) =
        covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) g₁ g) := by
    unfold covariantJetNormSq
    apply Finset.sum_congr rfl
    intro i _
    rw [norm_iteratedCovGrad_connectionDifferenceLoweredCc_eq_connectionDifferenceSection
      (I := I) (M := M) g g₁ i]
  rw [← heq]
  exact hlower g₁ P hP htie hδ_le hδ0 hδ R A hR hA hP2 hP3

private theorem ricciConnectionDifferenceQuadratic_action_tame_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g g₁) W) ≤
        (D R * A ^ 2) ^ 2 := by
  obtain ⟨Bc, hBc, hconn⟩ :=
    conn_h2_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Kt, hKt, htrace⟩ :=
    fourtrace_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Caa, hCaa, haa⟩ :=
    aa_h2_of (I := I) (M := M) hDim g
  obtain ⟨Capp, hCapp, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 2 2
  let Z : ℝ → ℝ := fun R =>
    Capp * Caa * (Kt * (1 + R ^ 2)) * (Bc R) ^ 4 * R ^ 2
  let D : ℝ → ℝ := fun R => Real.sqrt (Z R)
  refine ⟨D, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P W hP htie δ hδ_le hδ0 hδ R A hR hA hP2 hP3 hW2
  have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
  have hBR : 0 ≤ Bc R := hBc R hR
  have hQt0 : 0 ≤ Kt * (1 + R ^ 2) :=
    mul_nonneg hKt (by positivity)
  have htrace' :
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciCometricFourTraceCastG0 (I := I) g g₁) ≤
        Kt * (1 + R ^ 2) := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciCometricFourTraceCastG0 (I := I) g g₁) ≤
        Kt * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) :=
          htrace g₁ P hP htie hδ_le hδ0 hδ
      _ ≤ Kt * (1 + R ^ 2) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hKt
  have hQ0 : 0 ≤ (Bc R * A) ^ 2 := sq_nonneg _
  have hcoeff :
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g g₁) ≤
        Caa * (Kt * (1 + R ^ 2)) * ((Bc R * A) ^ 2) ^ 2 :=
    haa g₁ ((Bc R * A) ^ 2) (Kt * (1 + R ^ 2))
      hQ0 hQt0
      (hconn g₁ P hP htie hδ_le hδ0 hδ R A hR hA hP2 hP3)
      htrace'
  have hW20 :
      0 ≤ covariantJetNormSq (I := I) (M := M) g 2 W :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have happ' :
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g g₁) W) ≤
        Capp *
          covariantJetNormSq (I := I) (M := M) g 2
            (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g g₁) *
          covariantJetNormSq (I := I) (M := M) g 2 W := by
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      happ (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g g₁) W
  have hmain :
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g g₁) W) ≤
        Capp *
            (Caa * (Kt * (1 + R ^ 2)) * ((Bc R * A) ^ 2) ^ 2) *
          R ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g g₁) W) ≤
        Capp *
            covariantJetNormSq (I := I) (M := M) g 2
              (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g g₁) *
          covariantJetNormSq (I := I) (M := M) g 2 W := happ'
      _ ≤ Capp *
            (Caa * (Kt * (1 + R ^ 2)) * ((Bc R * A) ^ 2) ^ 2) *
          covariantJetNormSq (I := I) (M := M) g 2 W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcoeff hCapp) hW20
      _ ≤ Capp *
            (Caa * (Kt * (1 + R ^ 2)) * ((Bc R * A) ^ 2) ^ 2) *
          R ^ 2 := by
        exact mul_le_mul_of_nonneg_left hW2
          (mul_nonneg hCapp
            (mul_nonneg
              (mul_nonneg hCaa hQt0)
              (sq_nonneg _)))
  have hZ0 : 0 ≤ Z R := by
    dsimp only [Z]
    positivity
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2
          (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g g₁) W) ≤
      Capp *
          (Caa * (Kt * (1 + R ^ 2)) * ((Bc R * A) ^ 2) ^ 2) *
        R ^ 2 := hmain
    _ = Z R * (A ^ 2) ^ 2 := by
      simp only [Z]
      ring
    _ = (D R) ^ 2 * (A ^ 2) ^ 2 := by
      rw [show (D R) ^ 2 = Z R by
        simpa only [D] using Real.sq_sqrt hZ0]
    _ = (D R * A ^ 2) ^ 2 := by ring

private theorem full_slot_h3_rf
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 3
          (slotInsertEndoCc (I := I) (M := M) g s
            (metricComparisonEndomorphismField (I := I) (M := M) g g₁)) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) := by
  obtain ⟨K₀, hK₀, hsharp⟩ :=
    sharp_h3_rf (I := I) (M := M) g hδ₀0 hδ₀
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := fr ^ s * K₀
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K := mul_nonneg (pow_nonneg hfr s) hK₀
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  calc
    covariantJetNormSq (I := I) (M := M) g 3
        (slotInsertEndoCc (I := I) (M := M) g s
          (metricComparisonEndomorphismField (I := I) (M := M) g g₁)) ≤
      fr ^ s * covariantJetNormSq (I := I) (M := M) g 3
        (slotInsertEndoCc (I := I) (M := M) g 0
          (metricComparisonEndomorphismField (I := I) (M := M) g g₁)) := by
      simpa only [fr] using endo_slot_h3 (I := I) (M := M) g s
        (metricComparisonEndomorphismField (I := I) (M := M) g g₁)
    _ = fr ^ s * covariantJetNormSq (I := I) (M := M) g 3
        (sharpFlatEndoCc (I := I) g g₁) := by
      rw [sharp_eq_slot0 (I := I) (M := M) g g₁]
    _ ≤ fr ^ s * (K₀ *
        (1 + covariantJetNormSq (I := I) (M := M) g 3 P)) :=
      mul_le_mul_of_nonneg_left
        (hsharp g₁ P hP htie hδ_le hδ0 hδ) (pow_nonneg hfr s)
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) := by
      simp only [K]
      ring

private def H3Poly
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s : ℕ} (n : ℕ) (K : ℝ) (S : SmoothCcTensor g r s) : Prop :=
  0 ≤ K ∧
    covariantJetNormSq (I := I) (M := M) g 3 S ≤
      K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ n

omit [CompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem h3p_const
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s : ℕ} (S : SmoothCcTensor g r s) :
    H3Poly (I := I) (M := M) g P 0
      (covariantJetNormSq (I := I) (M := M) g 3 S) S := by
  refine ⟨covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g S, ?_⟩
  rw [pow_zero, mul_one]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem h3p_app_of
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {p r c n m : ℕ} {A B : ℝ}
    {Φ : SmoothCcTensor g r c} {W : SmoothCcTensor g p r}
    (C : ℝ) (hC : 0 ≤ C)
    (happ : covariantJetNormSq (I := I) (M := M) g 3
          (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
        C * covariantJetNormSq (I := I) (M := M) g 3 Φ *
          covariantJetNormSq (I := I) (M := M) g 3 W)
    (hΦ : H3Poly (I := I) (M := M) g P n A Φ)
    (hW : H3Poly (I := I) (M := M) g P m B W) :
    H3Poly (I := I) (M := M) g P (n + m) (C * A * B)
      (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) := by
  let X : ℝ := 1 + covariantJetNormSq (I := I) (M := M) g 3 P
  have hX : 0 ≤ X := by
    dsimp only [X]
    linarith [covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g P]
  refine ⟨mul_nonneg (mul_nonneg hC hΦ.1) hW.1, ?_⟩
  calc
    covariantJetNormSq (I := I) (M := M) g 3
        (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
      C * covariantJetNormSq (I := I) (M := M) g 3 Φ *
        covariantJetNormSq (I := I) (M := M) g 3 W := happ
    _ ≤ C * (A * X ^ n) *
        covariantJetNormSq (I := I) (M := M) g 3 W := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hΦ.2 hC)
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g W)
    _ ≤ C * (A * X ^ n) * (B * X ^ m) := by
      exact mul_le_mul_of_nonneg_left hW.2
        (mul_nonneg hC (mul_nonneg hΦ.1 (pow_nonneg hX n)))
    _ = (C * A * B) *
        (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ (n + m) := by
      rw [pow_add]
      simp only [X]
      ring

theorem exists_connectionDifferenceLowOrderOperator_covariantJetNormSq_three_radiusFree_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 3
          (connectionDifferenceLowOrderOperator (I := I) (M := M) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) := by
  obtain ⟨Ks, hKs, hslot⟩ :=
    full_slot_h3_rf (I := I) (M := M) g 2 hδ₀0 hδ₀
  obtain ⟨C, hC, happ⟩ :=
    app_h3_mul (I := I) (M := M) hDim g 3 3 3
  let Kk : ℝ := covariantJetNormSq (I := I) (M := M) g 3
    (koszulOp (I := I) (M := M) g)
  let Kp : ℝ := covariantJetNormSq (I := I) (M := M) g 3
    (permCoeff (I := I) (M := M) g connectionDifferenceLowOrderPermutation)
  let Ki : ℝ := C * Ks * Kk
  let K : ℝ := C * Kp * Ki
  have hKk : 0 ≤ Kk := covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g _
  have hKp : 0 ≤ Kp := covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g _
  have hKi : 0 ≤ Ki := mul_nonneg (mul_nonneg hC hKs) hKk
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hC hKp) hKi
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hs :
      H3Poly (I := I) (M := M) g P 1 Ks
        (slotInsertEndoCc (I := I) (M := M) g 2
          (metricComparisonEndomorphismField (I := I) (M := M) g g₁)) := by
    refine ⟨hKs, ?_⟩
    simpa only [H3Poly, pow_one] using
      hslot g₁ P hP htie hδ_le hδ0 hδ
  have hk :
      H3Poly (I := I) (M := M) g P 0 Kk
        (koszulOp (I := I) (M := M) g) := by
    simpa only [Kk] using h3p_const (I := I) (M := M) g P
      (koszulOp (I := I) (M := M) g)
  have hi :
      H3Poly (I := I) (M := M) g P 1 Ki
        (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
          (slotInsertEndoCc (I := I) (M := M) g 2
            (metricComparisonEndomorphismField (I := I) (M := M) g g₁))
          (koszulOp (I := I) (M := M) g)) := by
    simpa only [Ki, Nat.reduceAdd] using
      h3p_app_of (I := I) (M := M) g P C hC (happ _ _) hs hk
  have hp :
      H3Poly (I := I) (M := M) g P 0 Kp
        (permCoeff (I := I) (M := M) g connectionDifferenceLowOrderPermutation) := by
    simpa only [Kp] using h3p_const (I := I) (M := M) g P
      (permCoeff (I := I) (M := M) g connectionDifferenceLowOrderPermutation)
  have hout :=
    h3p_app_of (I := I) (M := M) g P C hC (happ _ _) hp hi
  simpa only [K, connectionDifferenceLowOrderOperator, Nat.zero_add, H3Poly, pow_one] using hout.2

theorem exists_ricciConnectionDerivativeCoefficient_covariantJetNormSq_two_radiusFree_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDerivativeCoefficient (I := I) (M := M) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) := by
  obtain ⟨Kc, hKc, hconn⟩ :=
    exists_connectionDifferenceLowOrderOperator_covariantJetNormSq_three_radiusFree_bound (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨C, hC, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 3 4 4
  let Kp : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciConnectionDifferenceDerivativeCyclicPermutation)
  let K : ℝ := C * Kp * Kc
  have hKp : 0 ≤ Kp := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hC hKp) hKc
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hp :
      H2Poly (I := I) (M := M) g P 0 Kp
        (permCoeff (I := I) (M := M) g ricciConnectionDifferenceDerivativeCyclicPermutation) := by
    simpa only [Kp] using hp_const (I := I) (M := M) g P
      (permCoeff (I := I) (M := M) g ricciConnectionDifferenceDerivativeCyclicPermutation)
  have hg :
      H2Poly (I := I) (M := M) g P 1 Kc
        (covGrad (I := I) (M := M) g 3 3
          (connectionDifferenceLowOrderOperator (I := I) (M := M) g g₁)) := by
    refine ⟨hKc, ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g 3 3
            (connectionDifferenceLowOrderOperator (I := I) (M := M) g g₁)) ≤
        covariantJetNormSq (I := I) (M := M) g 3
          (connectionDifferenceLowOrderOperator (I := I) (M := M) g g₁) :=
        grad_h2_le_h3 (I := I) (M := M) g _
      _ ≤ Kc * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) :=
        hconn g₁ P hP htie hδ_le hδ0 hδ
      _ = Kc * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 1 := by
        rw [pow_one]
  have hout :=
    hp_app_of (I := I) (M := M) g P C hC (happ _ _) hp hg
  simpa only [K, ricciConnectionDerivativeCoefficient, Nat.zero_add, H2Poly, pow_one] using hout.2

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem gradP_hp
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2) :
    H2Poly (I := I) (M := M) g P 1 1
      (covGrad (I := I) (M := M) g 0 2 P) := by
  refine ⟨by norm_num, ?_⟩
  rw [one_mul, pow_one]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (covGrad (I := I) (M := M) g 0 2 P) ≤
      covariantJetNormSq (I := I) (M := M) g 3 P :=
      grad_h2_le_h3 (I := I) (M := M) g P
    _ ≤ 1 + covariantJetNormSq (I := I) (M := M) g 3 P := by linarith

private theorem dagAct_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 0 3 4
            (ricciConnectionDerivativeCoefficient (I := I) (M := M) g g₁)
            (covGrad (I := I) (M := M) g 0 2 P)) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 2 := by
  obtain ⟨Kd, hKd, hdag⟩ :=
    exists_ricciConnectionDerivativeCoefficient_covariantJetNormSq_two_radiusFree_bound (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨C, hC, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 3 4
  let K : ℝ := C * Kd
  have hK : 0 ≤ K := mul_nonneg hC hKd
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hd :
      H2Poly (I := I) (M := M) g P 1 Kd
        (ricciConnectionDerivativeCoefficient (I := I) (M := M) g g₁) := by
    refine ⟨hKd, ?_⟩
    simpa only [H2Poly, pow_one] using
      hdag g₁ P hP htie hδ_le hδ0 hδ
  have hPgrad := gradP_hp (I := I) (M := M) g P
  have hout :=
    hp_app_of (I := I) (M := M) g P C hC (happ _ _) hd hPgrad
  simpa only [K, mul_one, Nat.reduceAdd, H2Poly] using hout.2

omit [NeZero (Module.finrank ℝ E)] in
private theorem domperm_l2_sq
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g 0 s i
        (domDomCongrSection (I := I) g σ S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g 0 s i S‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
    (I := I) (M := M) g σ S i x

omit [NeZero (Module.finrank ℝ E)] in
private theorem domperm_h2
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    covariantJetNormSq (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g σ S) =
      covariantJetNormSq (I := I) (M := M) g 2 S := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro i _
  exact domperm_l2_sq (I := I) (M := M) g σ S i

private theorem rsperm_l2_sq
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g r s i
        (rsDomDomCongrSection (I := I) (M := M) g r s σ S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s i S‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (I := I) (M := M) g r s σ S
      (rsDomDomCongrSection (I := I) (M := M) g r s σ S)
      (fun y d => by
        rw [rsDomDomCongrSection_toSection,
          toModel_rsDomDomCongr_apply]) i x

private theorem rsperm_h2
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g 2
        (rsDomDomCongrSection (I := I) (M := M) g r s σ S) =
      covariantJetNormSq (I := I) (M := M) g 2 S := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro i _
  exact rsperm_l2_sq (I := I) (M := M) g σ S i

omit [NeZero (Module.finrank ℝ E)] in
private theorem hp_domperm
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {s n : ℕ} {A : ℝ} {S : SmoothCcTensor g 0 s}
    (σ : Equiv.Perm (Fin s))
    (hS : H2Poly (I := I) (M := M) g P n A S) :
    H2Poly (I := I) (M := M) g P n A
      (domDomCongrSection (I := I) g σ S) := by
  refine ⟨hS.1, ?_⟩
  rw [domperm_h2]
  exact hS.2

private theorem hp_rsperm
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s n : ℕ} {A : ℝ} {S : SmoothCcTensor g r s}
    (σ : Equiv.Perm (Fin s))
    (hS : H2Poly (I := I) (M := M) g P n A S) :
    H2Poly (I := I) (M := M) g P n A
      (rsDomDomCongrSection (I := I) (M := M) g r s σ S) := by
  refine ⟨hS.1, ?_⟩
  rw [rsperm_h2]
  exact hS.2

private theorem slot_iter2_h2
    (g : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4) :
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtendIter (I := I) (M := M) g 0 4 2 G) ≤
      (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          covariantJetNormSq (I := I) (M := M) g 2 G) := by
  change covariantJetNormSq (I := I) (M := M) g 2
      (slotExtend (I := I) (M := M) g 1 5
        (slotExtend (I := I) (M := M) g 0 4 G)) ≤ _
  have hfr : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4 G)) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 4 G) :=
      slot_h2 (I := I) (M := M) g 1 5 _
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          covariantJetNormSq (I := I) (M := M) g 2 G) :=
      mul_le_mul_of_nonneg_left
        (slot_h2 (I := I) (M := M) g 0 4 G) hfr

private def lowMonoPerm (σ : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 6) :=
  ((finSumFinEquiv (m := 4) (n := 2)).permCongr
    (Equiv.sumCongr σ (Equiv.refl (Fin 2)))).trans deTurckLieCovariantDerivativePairTracePermutation

private lemma lowMonoPerm_cast (σ : Equiv.Perm (Fin 4)) (j : Fin 4) :
    lowMonoPerm σ (Fin.castAdd 2 j) =
      (![1, 3, 4, 5] : Fin 4 → Fin 6) (σ j) := by
  have hpad : (finSumFinEquiv (m := 4) (n := 2)).permCongr
      (Equiv.sumCongr σ (Equiv.refl (Fin 2))) (Fin.castAdd 2 j) =
      Fin.castAdd 2 (σ j) := by
    rw [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd]
    rfl
  rw [lowMonoPerm, Equiv.trans_apply, hpad]
  have hsigma : ∀ k : Fin 4,
      deTurckLieCovariantDerivativePairTracePermutation (Fin.castAdd 2 k) =
        (![1, 3, 4, 5] : Fin 4 → Fin 6) k := by
    intro k
    fin_cases k <;> decide
  exact hsigma (σ j)

private lemma lowMonoPerm_nat (σ : Equiv.Perm (Fin 4)) (k : Fin 2) :
    lowMonoPerm σ (Fin.natAdd 4 k) =
      (![0, 2] : Fin 2 → Fin 6) k := by
  have hpad : (finSumFinEquiv (m := 4) (n := 2)).permCongr
      (Equiv.sumCongr σ (Equiv.refl (Fin 2))) (Fin.natAdd 4 k) =
      Fin.natAdd 4 k := by
    rw [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_natAdd]
    rfl
  rw [lowMonoPerm, Equiv.trans_apply, hpad]
  have hsigma : ∀ k' : Fin 2,
      deTurckLieCovariantDerivativePairTracePermutation (Fin.natAdd 4 k') =
        (![0, 2] : Fin 2 → Fin 6) k' := by
    intro k'
    fin_cases k' <;> decide
  exact hsigma k

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] in
private lemma zeroRank_decomp (x : M) (t : Tensor0SSpace 0 I x) :
    t = (Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0)) •
      unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [show m = (fun i : Fin 0 => i.elim0 : Fin 0 → E) from by
    funext k
    exact k.elim0]
  rw [Tensor0SSpace.toModel_smul, smul_apply]
  rw [show Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x)
      (fun i : Fin 0 => i.elim0) = 1 from by
    rw [unitTensor, Tensor0SSpace.toModel_ofModel]
    rfl]
  rw [smul_eq_mul, mul_one]


omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem curvMono_pair
    (g g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (σ : Equiv.Perm (Fin 4)) :
    curvatureDecompositionMonomialCoeffField (I := I) (M := M) g g₁
        (ccTensorUnitValueSection (I := I) (M := M) g S)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g S) σ =
      ccOperatorFieldComp (I := I) (M := M) g 4 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g g₁)
        (rsDomDomCongrSection (I := I) (M := M) g 4 6
          (lowMonoPerm σ)
          (slotExtendIter (I := I) (M := M) g 0 2 4 S)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro G
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g 4 6
        (lowMonoPerm σ)
        (slotExtendIter (I := I) (M := M) g 0 2 4 S)).toSection x) G
      with hY_def
  have hYval : ∀ w : Fin 6 → E,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel G
            (fun j : Fin 4 =>
              w ((![1, 3, 4, 5] : Fin 4 → Fin 6) (σ j))) *
          unitModel (I := I) (M := M) g 2 S x ![w 0, w 2] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g 4 6
          (lowMonoPerm σ)
          (slotExtendIter (I := I) (M := M) g 0 2 4 S)).toSection x) G) =
        ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 6 I x from
          rsDomDomCongr (lowMonoPerm σ)
            ((slotExtendIter (I := I) (M := M) g 0 2 4 S).toSection x)) G)
        from by rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M)
      (lowMonoPerm σ)
      ((slotExtendIter (I := I) (M := M) g 0 2 4 S).toSection x) G]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hslot := slotExtendIter_four_toModel (I := I) (M := M) g S x G
      (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
        (w (lowMonoPerm σ i)))
    change Tensor0SSpace.toModel
        ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g 0 2 4 S).toSection x) G)
          (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
              (w (lowMonoPerm σ i)))) =
      Tensor0SSpace.toModel G
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                (w (lowMonoPerm σ 0))),
            tangentSpaceModelContinuousLinearEquiv (I := I) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                (w (lowMonoPerm σ 1))),
            tangentSpaceModelContinuousLinearEquiv (I := I) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                (w (lowMonoPerm σ 2))),
            tangentSpaceModelContinuousLinearEquiv (I := I) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                (w (lowMonoPerm σ 3)))] *
        unitModel (I := I) (M := M) g 2 S x
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
              (w (lowMonoPerm σ (Fin.natAdd 4 k))))) at hslot
    simp only [ContinuousLinearEquiv.apply_symm_apply] at hslot
    rw [hslot]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext j
      fin_cases j
      · exact congrArg w (lowMonoPerm_cast σ 0)
      · exact congrArg w (lowMonoPerm_cast σ 1)
      · exact congrArg w (lowMonoPerm_cast σ 2)
      · exact congrArg w (lowMonoPerm_cast σ 3)
    · refine congrArg _ ?_
      funext k
      fin_cases k
      · exact congrArg w (lowMonoPerm_nat σ 0)
      · exact congrArg w (lowMonoPerm_nat σ 1)
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (curvatureDecompositionMonomialCoeffField (I := I) (M := M) g g₁
          (ccTensorUnitValueSection (I := I) (M := M) g S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g S)
          σ).toSection x) G) v =
      ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel
              (ccTensorUnitValueSection (I := I) (M := M) g S x)
              ![(smoothOrthoFrame (I := I) g₁ x a x : E),
                (smoothOrthoFrame (I := I) g₁ x b x : E)] *
            Tensor0SSpace.toModel G
              (fun i =>
                (Fin.cons
                  ((smoothOrthoFrame (I := I) g₁ x a x : E))
                  (Fin.cons
                    ((smoothOrthoFrame (I := I) g₁ x b x : E)) v) :
                  Fin 4 → E) (σ i)) := by
    rw [show ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (curvatureDecompositionMonomialCoeffField (I := I) (M := M) g g₁
          (ccTensorUnitValueSection (I := I) (M := M) g S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g S)
          σ).toSection x) G) =
        curvatureDecompositionMonomialFibFixedFrame (I := I) (M := M)
          (ccTensorUnitValueSection (I := I) (M := M) g S) σ
          (smoothOrthoFrame (I := I) g₁ x) x G from rfl]
    exact curvatureDecompositionMonomialFibFixedFrame_toModel
      (I := I) (M := M)
      (ccTensorUnitValueSection (I := I) (M := M) g S) σ
      (smoothOrthoFrame (I := I) g₁ x) x G v
  have hRHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ccOperatorFieldComp (I := I) (M := M) g 4 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g g₁)
          (rsDomDomCongrSection (I := I) (M := M) g 4 6
            (lowMonoPerm σ)
            (slotExtendIter (I := I) (M := M) g 0 2 4 S))).toSection x)
        G) v =
      ∑ b : Fin (Module.finrank ℝ E),
        ∑ a : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel Y
            (Fin.cons
              ((smoothOrthoFrame (I := I) g₁ x a x :
                TangentSpace I x) : E)
              (Fin.cons
                ((smoothOrthoFrame (I := I) g₁ x a x :
                  TangentSpace I x) : E)
                (Fin.cons
                  ((smoothOrthoFrame (I := I) g₁ x b x :
                    TangentSpace I x) : E)
                  (Fin.cons
                    ((smoothOrthoFrame (I := I) g₁ x b x :
                      TangentSpace I x) : E)
                    (fun j => (v j : E)))))) := by
    rw [show ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ccOperatorFieldComp (I := I) (M := M) g 4 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g g₁)
          (rsDomDomCongrSection (I := I) (M := M) g 4 6
            (lowMonoPerm σ)
            (slotExtendIter (I := I) (M := M) g 0 2 4 S))).toSection x)
        G) =
        cometricDoubleTraceFib (I := I) g₁ 2 x
          (cometricDoubleTraceFib (I := I) g₁ 4 x Y) from by
      rw [hY_def, operatorFieldComposition_toSection]
      rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₁ 2 x]
    rw [modelDoubleTrace_apply (E := E) 2
      (cometricLmodel (I := I) g₁ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag
      (I := I) g₁ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        (cometricDoubleTraceFib (I := I) g₁ 4 x Y))
      (fun j => (v j : E))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [cometricDoubleTraceFib_toModel (I := I) g₁ 4 x Y]
    rw [modelDoubleTrace_apply (E := E) 4
      (cometricLmodel (I := I) g₁ x)]
    exact cometric_dualTrace_eq_orthoFrame_diag
      (I := I) g₁ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel Y)
      (Fin.cons
        ((smoothOrthoFrame (I := I) g₁ x b x :
          TangentSpace I x) : E)
        (Fin.cons
          ((smoothOrthoFrame (I := I) g₁ x b x :
            TangentSpace I x) : E)
          (fun j => (v j : E))))
  rw [hLHS, hRHS, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hYval, mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine congrArg _ ?_
    funext i
    have htuple : ∀ k : Fin 4,
        (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : E))
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : E)) v) :
          Fin 4 → E) k =
        ((Fin.cons
          ((smoothOrthoFrame (I := I) g₁ x a x :
            TangentSpace I x) : E)
          (Fin.cons
            ((smoothOrthoFrame (I := I) g₁ x a x :
              TangentSpace I x) : E)
            (Fin.cons
              ((smoothOrthoFrame (I := I) g₁ x b x :
                TangentSpace I x) : E)
              (Fin.cons
                ((smoothOrthoFrame (I := I) g₁ x b x :
                  TangentSpace I x) : E)
                (fun j => (v j : E)))))) : Fin 6 → E)
          ((![1, 3, 4, 5] : Fin 4 → Fin 6) k) := by
      intro k
      fin_cases k <;> rfl
    exact htuple (σ i)
  · have hWm : Tensor0SSpace.toModel
        (ccTensorUnitValueSection (I := I) (M := M) g S x) =
        unitModel (I := I) (M := M) g 2 S x := rfl
    rw [hWm]
    refine congrArg _ ?_
    funext j
    fin_cases j <;> rfl

private theorem slot_iter4_h2
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) :
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtendIter (I := I) (M := M) g 0 2 4 S) ≤
      (Module.finrank ℝ E : ℝ) ^ 4 *
        covariantJetNormSq (I := I) (M := M) g 2 S := by
  change covariantJetNormSq (I := I) (M := M) g 2
      (slotExtend (I := I) (M := M) g 3 5
        (slotExtend (I := I) (M := M) g 2 4
          (slotExtend (I := I) (M := M) g 1 3
            (slotExtend (I := I) (M := M) g 0 2 S)))) ≤ _
  have hfr : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
  calc
    _ ≤ (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 2 4
            (slotExtend (I := I) (M := M) g 1 3
              (slotExtend (I := I) (M := M) g 0 2 S))) :=
      slot_h2 (I := I) (M := M) g 3 5 _
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          covariantJetNormSq (I := I) (M := M) g 2
            (slotExtend (I := I) (M := M) g 1 3
              (slotExtend (I := I) (M := M) g 0 2 S))) :=
      mul_le_mul_of_nonneg_left
        (slot_h2 (I := I) (M := M) g 2 4 _) hfr
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) *
            covariantJetNormSq (I := I) (M := M) g 2
              (slotExtend (I := I) (M := M) g 0 2 S))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (slot_h2 (I := I) (M := M) g 1 3 _) hfr) hfr
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) *
              covariantJetNormSq (I := I) (M := M) g 2 S))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (slot_h2 (I := I) (M := M) g 0 2 S) hfr) hfr) hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 4 *
        covariantJetNormSq (I := I) (M := M) g 2 S := by ring

private theorem curvMono_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (S : SmoothCcTensor g 0 2) (σ : Equiv.Perm (Fin 4)),
        covariantJetNormSq (I := I) (M := M) g 2
            (curvatureDecompositionMonomialCoeffField (I := I) (M := M) g g₁
              (ccTensorUnitValueSection (I := I) (M := M) g S)
              (ccTensorUnitValueSection_contMDiff
                (I := I) (M := M) g S) σ) ≤
          C * covariantJetNormSq (I := I) (M := M) g 2
              (cometricDoublePairTraceCoefficient (I := I) (M := M) g g₁) *
            covariantJetNormSq (I := I) (M := M) g 2 S := by
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 4 6 2
  let fr : ℝ := Module.finrank ℝ E
  let C : ℝ := Ca * fr ^ 4
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨C, mul_nonneg hCa (pow_nonneg hfr 4), ?_⟩
  intro g₁ S σ
  rw [curvMono_pair (I := I) (M := M) g g₁ S σ]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g 4 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g g₁)
          (rsDomDomCongrSection (I := I) (M := M) g 4 6
            (lowMonoPerm σ)
            (slotExtendIter (I := I) (M := M) g 0 2 4 S))) ≤
      Ca * covariantJetNormSq (I := I) (M := M) g 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g g₁) *
        covariantJetNormSq (I := I) (M := M) g 2
          (rsDomDomCongrSection (I := I) (M := M) g 4 6
            (lowMonoPerm σ)
            (slotExtendIter (I := I) (M := M) g 0 2 4 S)) :=
      happ _ _
    _ = Ca * covariantJetNormSq (I := I) (M := M) g 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g g₁) *
        covariantJetNormSq (I := I) (M := M) g 2
          (slotExtendIter (I := I) (M := M) g 0 2 4 S) := by
      rw [rsperm_h2]
    _ ≤ Ca * covariantJetNormSq (I := I) (M := M) g 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g g₁) *
        (fr ^ 4 * covariantJetNormSq (I := I) (M := M) g 2 S) :=
      mul_le_mul_of_nonneg_left
        (slot_iter4_h2 (I := I) (M := M) g S)
        (mul_nonneg hCa
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _))
    _ = C * covariantJetNormSq (I := I) (M := M) g 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g g₁) *
        covariantJetNormSq (I := I) (M := M) g 2 S := by
      simp only [C, fr]
      ring

private theorem decomposition_sobolev_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (G : SmoothCcTensor g 0 4) (σ : Equiv.Perm (Fin 4)),
        covariantJetNormSq (I := I) (M := M) g 2
            (decompositionKernelContractionMonomialField
              (I := I) (M := M) g g G σ) ≤
          K * covariantJetNormSq (I := I) (M := M) g 2 G := by
  obtain ⟨C, hC, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 6 2
  let Km : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (movingMetricPairTraceOperator (I := I) (M := M) g g)
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := C * Km * (fr * fr)
  have hKm : 0 ≤ Km := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K :=
    mul_nonneg (mul_nonneg hC hKm) (mul_nonneg hfr hfr)
  refine ⟨K, hK, ?_⟩
  intro G σ
  let τ : Equiv.Perm (Fin 4) :=
    Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ
  let D : SmoothCcTensor g 0 4 :=
    domDomCongrSection (I := I) g τ G
  let S : SmoothCcTensor g 2 6 :=
    slotExtendIter (I := I) (M := M) g 0 4 2 D
  let R : SmoothCcTensor g 2 6 :=
    rsDomDomCongrSection (I := I) (M := M) g 2 6 movingMetricPairTracePermutation S
  have hD :
      covariantJetNormSq (I := I) (M := M) g 2 D =
        covariantJetNormSq (I := I) (M := M) g 2 G := by
    simpa only [D, τ] using
      domperm_h2 (I := I) (M := M) g τ G
  have hS :
      covariantJetNormSq (I := I) (M := M) g 2 S ≤
        fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 D) := by
    simpa only [S, fr] using
      slot_iter2_h2 (I := I) (M := M) g D
  have hR :
      covariantJetNormSq (I := I) (M := M) g 2 R =
        covariantJetNormSq (I := I) (M := M) g 2 S := by
    simpa only [R] using
      rsperm_h2 (I := I) (M := M) g movingMetricPairTracePermutation S
  have href :
      decompositionKernelContractionMonomialField
          (I := I) (M := M) g g G σ =
        ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (movingMetricPairTraceOperator (I := I) (M := M) g g) R := by
    have htrace : secondMetricPairTraceOperator (I := I) (M := M) g g =
        movingMetricPairTraceOperator (I := I) (M := M) g g := by
      apply SmoothCcTensor.ext
      apply ContMDiffSection.ext
      intro x
      rfl
    have hperm : ricciFoldRemainderSlotPerm = movingMetricPairTracePermutation := by
      rfl
    have hbase :=
      decompositionKernelContractionMonomialField_eq_movingMetricPairTraceOperator_comp
        (I := I) (M := M) g g G σ
    rw [htrace, hperm] at hbase
    simpa only [R, S, D, τ] using hbase
  rw [href]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (movingMetricPairTraceOperator (I := I) (M := M) g g) R) ≤
      C * covariantJetNormSq (I := I) (M := M) g 2
          (movingMetricPairTraceOperator (I := I) (M := M) g g) *
        covariantJetNormSq (I := I) (M := M) g 2 R :=
      happ _ _
    _ = C * Km * covariantJetNormSq (I := I) (M := M) g 2 S := by
      rw [hR]
    _ ≤ C * Km * (fr *
        (fr * covariantJetNormSq (I := I) (M := M) g 2 D)) :=
      mul_le_mul_of_nonneg_left hS (mul_nonneg hC hKm)
    _ = K * covariantJetNormSq (I := I) (M := M) g 2 G := by
      rw [hD]
      simp only [K]
      ring

private theorem ricciCovariantDerivativeConnectionDifference_secondOrder_radiusFree_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g g₁ P) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 3 := by
  obtain ⟨Kg, hKg, hG⟩ :=
    dagAct_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ke, hKe, hE⟩ :=
    full_slot_h3_rf (I := I) (M := M) g 1 hδ₀0 hδ₀
  obtain ⟨Cr, hCr, href⟩ :=
    decomposition_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 2 2
  let Km : ℝ := Ca * (Cr * Kg) * Ke
  let K : ℝ := 2 * (Km + Km)
  have hKm : 0 ≤ Km :=
    mul_nonneg (mul_nonneg hCa (mul_nonneg hCr hKg)) hKe
  have hK : 0 ≤ K :=
    mul_nonneg (by norm_num) (add_nonneg hKm hKm)
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  let G : SmoothCcTensor g 0 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 0 3 4
      (ricciConnectionDerivativeCoefficient (I := I) (M := M) g g₁)
      (covGrad (I := I) (M := M) g 0 2 P)
  let Eop : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g g₁)
  have hGp :
      H2Poly (I := I) (M := M) g P 2 Kg G := by
    refine ⟨hKg, ?_⟩
    simpa only [G, H2Poly] using
      hG g₁ P hP htie hδ_le hδ0 hδ
  have hEp :
      H2Poly (I := I) (M := M) g P 1 Ke Eop := by
    refine ⟨hKe, ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2 Eop ≤
        covariantJetNormSq (I := I) (M := M) g 3 Eop :=
        covariantJetNormSq_mono (I := I) (M := M) g (by omega : 2 ≤ 3) Eop
      _ ≤ Ke * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) :=
        hE g₁ P hP htie hδ_le hδ0 hδ
      _ = Ke * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 1 := by
        rw [pow_one]
  have hRp (σ : Equiv.Perm (Fin 4)) :
      H2Poly (I := I) (M := M) g P 2 (Cr * Kg)
        (decompositionKernelContractionMonomialField
          (I := I) (M := M) g g G σ) := by
    refine ⟨mul_nonneg hCr hKg, ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (decompositionKernelContractionMonomialField
            (I := I) (M := M) g g G σ) ≤
        Cr * covariantJetNormSq (I := I) (M := M) g 2 G :=
        href G σ
      _ ≤ Cr * (Kg *
          (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 2) :=
        mul_le_mul_of_nonneg_left hGp.2 hCr
      _ = (Cr * Kg) *
          (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 2 := by ring
  have hmono (σ : Equiv.Perm (Fin 4)) :
      H2Poly (I := I) (M := M) g P 3 Km
        (ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g g₁ G σ) := by
    simpa only [Km, ricciConnectionDifferenceDerivativeContractionMonomial, Nat.reduceAdd] using
      hp_app_of (I := I) (M := M) g P Ca hCa (happ _ _)
        (hRp σ) hEp
  have hsub :=
    hp_sub (I := I) (M := M) g P
      (hmono ricciConnectionDifferenceDerivativeCyclicPermutation) (hmono ricciConnectionDifferenceDerivativeFirstPairSwap)
  simpa only [K, ricciCovariantDerivativeConnectionDifferenceLowOrder, ricciConnectionDifferenceDerivativeContraction, G, Nat.reduceAdd, H2Poly] using hsub.2

private theorem ricciCovariantDerivativeConnectionDifference_action_tame_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g g₁ P) W) ≤
        (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨Kd, hKd, hdag⟩ :=
    exists_ricciConnectionDerivativeCoefficient_covariantJetNormSq_two_radiusFree_bound (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Cg, hCg, happG⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 3 4
  obtain ⟨Cr, hCr, href⟩ :=
    decomposition_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ke, hKe, hendo⟩ :=
    full_slot_h2_low (I := I) (M := M) g 1 hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happA⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 2 2
  obtain ⟨Co, hCo, happO⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 2 2
  let B : ℝ → ℝ := fun R =>
    Co * (4 * Ca * Cr * Cg * Kd * Ke * (1 + R ^ 2)) * R ^ 2
  let D : ℝ → ℝ := fun R => Real.sqrt (B R)
  refine ⟨D, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P W hP htie δ hδ_le hδ0 hδ R A hR hA hP2 hP3 hW2
  have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
  have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
  have hX0 : 0 ≤ 1 + R ^ 2 := by positivity
  have hDag :
      H2Poly (I := I) (M := M) g P 0 (Kd * (1 + A ^ 2))
        (ricciConnectionDerivativeCoefficient (I := I) (M := M) g g₁) := by
    refine ⟨mul_nonneg hKd (by positivity), ?_⟩
    simpa only [H2Poly, pow_zero, mul_one] using
      (hdag g₁ P hP htie hδ_le hδ0 hδ).trans
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hP3) hKd)
  have hGrad :
      H2Poly (I := I) (M := M) g P 0 (A ^ 2)
        (covGrad (I := I) (M := M) g 0 2 P) := by
    refine ⟨hA2, ?_⟩
    simpa only [H2Poly, pow_zero, mul_one] using
      (grad_h2_le_h3 (I := I) (M := M) g P).trans hP3
  let G : SmoothCcTensor g 0 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 0 3 4
      (ricciConnectionDerivativeCoefficient (I := I) (M := M) g g₁)
      (covGrad (I := I) (M := M) g 0 2 P)
  have hG :
      H2Poly (I := I) (M := M) g P 0
        (Cg * (Kd * (1 + A ^ 2)) * A ^ 2) G := by
    simpa only [G, Nat.zero_add] using
      hp_app_of (I := I) (M := M) g P Cg hCg
        (happG _ _) hDag hGrad
  have hRef (σ : Equiv.Perm (Fin 4)) :
      H2Poly (I := I) (M := M) g P 0
        (Cr * (Cg * (Kd * (1 + A ^ 2)) * A ^ 2))
        (decompositionKernelContractionMonomialField
          (I := I) (M := M) g g G σ) := by
    refine ⟨mul_nonneg hCr hG.1, ?_⟩
    simpa only [H2Poly, pow_zero, mul_one] using
      (href G σ).trans
        (mul_le_mul_of_nonneg_left hG.2 hCr)
  let Eop : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g g₁)
  have hE :
      H2Poly (I := I) (M := M) g P 0
        (Ke * (1 + R ^ 2)) Eop := by
    refine ⟨mul_nonneg hKe hX0, ?_⟩
    simpa only [H2Poly, pow_zero, mul_one, Eop] using
      (hendo g₁ P hP htie hδ_le hδ0 hδ).trans
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hP2) hKe)
  have hMono (σ : Equiv.Perm (Fin 4)) :
      H2Poly (I := I) (M := M) g P 0
        (Ca *
          (Cr * (Cg * (Kd * (1 + A ^ 2)) * A ^ 2)) *
          (Ke * (1 + R ^ 2)))
        (ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g g₁ G σ) := by
    simpa only [ricciConnectionDifferenceDerivativeContractionMonomial, Eop, Nat.zero_add] using
      hp_app_of (I := I) (M := M) g P Ca hCa
        (happA _ _) (hRef σ) hE
  have hDA :
      H2Poly (I := I) (M := M) g P 0
        (2 * (
          Ca * (Cr * (Cg * (Kd * (1 + A ^ 2)) * A ^ 2)) *
              (Ke * (1 + R ^ 2)) +
            Ca * (Cr * (Cg * (Kd * (1 + A ^ 2)) * A ^ 2)) *
              (Ke * (1 + R ^ 2))))
        (ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g g₁ P) := by
    simpa only [ricciCovariantDerivativeConnectionDifferenceLowOrder, ricciConnectionDifferenceDerivativeContraction, G] using
      hp_sub (I := I) (M := M) g P
        (hMono ricciConnectionDifferenceDerivativeCyclicPermutation) (hMono ricciConnectionDifferenceDerivativeFirstPairSwap)
  have hPass :
      H2Poly (I := I) (M := M) g P 0 (R ^ 2) W := by
    exact ⟨hR2, by
      simpa only [H2Poly, pow_zero, mul_one] using hW2⟩
  have hOut :=
    hp_app_of (I := I) (M := M) g P Co hCo
      (happO (ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g g₁ P) W)
      hDA hPass
  have hraw :
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g g₁ P) W) ≤
        B R * (1 + A ^ 2) * A ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g g₁ P) W) ≤
        Co *
          (2 * (
            Ca * (Cr * (Cg * (Kd * (1 + A ^ 2)) * A ^ 2)) *
                (Ke * (1 + R ^ 2)) +
              Ca * (Cr * (Cg * (Kd * (1 + A ^ 2)) * A ^ 2)) *
                (Ke * (1 + R ^ 2)))) *
          R ^ 2 := by
            simpa only [H2Poly, pow_zero, mul_one,
              operatorFieldComposition_zero_eq_operatorFieldApply, Nat.zero_add] using hOut.2
      _ = B R * (1 + A ^ 2) * A ^ 2 := by
        simp only [B]
        ring
  have hB0 : 0 ≤ B R := by
    dsimp only [B]
    positivity
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2
          (ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g g₁ P) W) ≤
      B R * (1 + A ^ 2) * A ^ 2 := hraw
    _ ≤ B R * (A + A ^ 2) ^ 2 := by
      have hscalar : (1 + A ^ 2) * A ^ 2 ≤ (A + A ^ 2) ^ 2 := by
        nlinarith only [sq_nonneg A, mul_nonneg hA (sq_nonneg A)]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hscalar hB0
    _ = (D R * (A + A ^ 2)) ^ 2 := by
      rw [mul_pow, show (D R) ^ 2 = B R by
        simpa only [D] using Real.sq_sqrt hB0]

private theorem ricciGood_act_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_hW : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g W x u v =
            ccTensorBilin (I := I) g W x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g g₁ P) W) ≤
        (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨Daa, hDaa, haa⟩ :=
    ricciConnectionDifferenceQuadratic_action_tame_bound (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Dda, hDda, hda⟩ :=
    ricciCovariantDerivativeConnectionDifference_action_tame_bound (I := I) (M := M) hDim g hδ₀0 hδ₀
  let Z : ℝ → ℝ := fun R => 2 * ((Daa R) ^ 2 + (Dda R) ^ 2)
  let D : ℝ → ℝ := fun R => Real.sqrt (Z R)
  refine ⟨D, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P W hP hW htie δ hδ_le hδ0 hδ R A hR hA hP2 hP3 hW2
  have hAA := haa g₁ P W hP htie hδ_le hδ0 hδ
    R A hR hA hP2 hP3 hW2
  have hDA := hda g₁ P W hP htie hδ_le hδ0 hδ
    R A hR hA hP2 hP3 hW2
  have hAB : A ^ 2 ≤ A + A ^ 2 := by linarith
  have hAAmono :
      (Daa R * A ^ 2) ^ 2 ≤
        (Daa R * (A + A ^ 2)) ^ 2 := by
    exact pow_le_pow_left₀
      (mul_nonneg (hDaa R hR) (sq_nonneg A))
      (mul_le_mul_of_nonneg_left hAB (hDaa R hR)) 2
  have hZ0 : 0 ≤ Z R := by
    dsimp only [Z]
    positivity
  rw [symmetrizedRicciConnectionDifferenceLowOrderCoefficient,
    ccInputSlotSymm_app (I := I) (M := M) g _ W hW,
    ricciConnectionDifferenceLowOrderCoefficient, operatorFieldApplication_add_left]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2
            (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g g₁) W +
          operatorFieldApply (I := I) (M := M) g 2 2
            (ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g g₁ P) W) ≤
      2 * (
        covariantJetNormSq (I := I) (M := M) g 2
            (operatorFieldApply (I := I) (M := M) g 2 2
              (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g g₁) W) +
          covariantJetNormSq (I := I) (M := M) g 2
            (operatorFieldApply (I := I) (M := M) g 2 2
              (ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g g₁ P) W)) :=
        covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _
    _ ≤ 2 * ((Daa R * A ^ 2) ^ 2 +
        (Dda R * (A + A ^ 2)) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hAA hDA) (by norm_num)
    _ ≤ 2 * ((Daa R * (A + A ^ 2)) ^ 2 +
        (Dda R * (A + A ^ 2)) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hAAmono le_rfl) (by norm_num)
    _ = Z R * (A + A ^ 2) ^ 2 := by
      simp only [Z]
      ring
    _ = (D R * (A + A ^ 2)) ^ 2 := by
      rw [mul_pow, show (D R) ^ 2 = Z R by
        simpa only [D] using Real.sq_sqrt hZ0]

private theorem inputSymm_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ C : SmoothCcTensor g 2 2,
        covariantJetNormSq (I := I) (M := M) g 2
            (ccInputSlotSymm (I := I) (M := M) g C) ≤
          K * covariantJetNormSq (I := I) (M := M) g 2 C := by
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 2 2
  let Ks : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (ccSlotSwapField (I := I) (M := M) g)
  let K : ℝ := 2 * (1 + Ca * Ks)
  have hKs : 0 ≤ Ks := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hK : 0 ≤ K :=
    mul_nonneg (by norm_num) (add_nonneg (by norm_num) (mul_nonneg hCa hKs))
  refine ⟨K, hK, ?_⟩
  intro C
  have hC0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g C
  have happ' :
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 2 2 2 C
            (ccSlotSwapField (I := I) (M := M) g)) ≤
        (Ca * Ks) * covariantJetNormSq (I := I) (M := M) g 2 C := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 2 2 2 C
            (ccSlotSwapField (I := I) (M := M) g)) ≤
        Ca * covariantJetNormSq (I := I) (M := M) g 2 C * Ks := by
        simpa only [Ks] using happ C
          (ccSlotSwapField (I := I) (M := M) g)
      _ = (Ca * Ks) * covariantJetNormSq (I := I) (M := M) g 2 C := by ring
  unfold ccInputSlotSymm
  rw [covariantJetNormSq_smul]
  have hsum0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (C + ccOperatorFieldComp (I := I) (M := M) g 2 2 2 C
      (ccSlotSwapField (I := I) (M := M) g))
  calc
    ((1 : ℝ) / 2) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2
          (C + ccOperatorFieldComp (I := I) (M := M) g 2 2 2 C
            (ccSlotSwapField (I := I) (M := M) g)) ≤
      covariantJetNormSq (I := I) (M := M) g 2
        (C + ccOperatorFieldComp (I := I) (M := M) g 2 2 2 C
          (ccSlotSwapField (I := I) (M := M) g)) := by
      nlinarith only [hsum0]
    _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 2 C +
        covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 2 2 2 C
            (ccSlotSwapField (I := I) (M := M) g))) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 2 C _
    _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 2 C +
        (Ca * Ks) * covariantJetNormSq (I := I) (M := M) g 2 C) :=
      mul_le_mul_of_nonneg_left
        (add_le_add le_rfl happ') (by norm_num)
    _ = K * covariantJetNormSq (I := I) (M := M) g 2 C := by
      simp only [K]
      ring

private theorem ricciGood_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g g₁ P) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 3 := by
  obtain ⟨Kaa, hKaa, haa⟩ :=
    ricciConnectionDifferenceQuadratic_secondOrder_radiusFree_bound (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Kda, hKda, hda⟩ :=
    ricciCovariantDerivativeConnectionDifference_secondOrder_radiusFree_bound (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Cs, hCs, hsymm⟩ :=
    inputSymm_h2 (I := I) (M := M) hDim g
  let Kl : ℝ := 2 * (Kaa + Kda)
  let K : ℝ := Cs * Kl
  have hKl : 0 ≤ Kl :=
    mul_nonneg (by norm_num) (add_nonneg hKaa hKda)
  have hK : 0 ≤ K := mul_nonneg hCs hKl
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hAA :
      H2Poly (I := I) (M := M) g P 3 Kaa
        (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g g₁) :=
    ⟨hKaa, haa g₁ P hP htie hδ_le hδ0 hδ⟩
  have hDA :
      H2Poly (I := I) (M := M) g P 3 Kda
        (ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g g₁ P) :=
    ⟨hKda, hda g₁ P hP htie hδ_le hδ0 hδ⟩
  have hlow :
      H2Poly (I := I) (M := M) g P 3 Kl
        (ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g g₁ P) := by
    simpa only [Kl, ricciConnectionDifferenceLowOrderCoefficient] using
      hp_add (I := I) (M := M) g P hAA hDA
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g g₁ P) =
      covariantJetNormSq (I := I) (M := M) g 2
        (ccInputSlotSymm (I := I) (M := M) g
          (ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g g₁ P)) := rfl
    _ ≤ Cs * covariantJetNormSq (I := I) (M := M) g 2
        (ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g g₁ P) :=
      hsymm _
    _ ≤ Cs * (Kl *
        (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 3) :=
      mul_le_mul_of_nonneg_left hlow.2 hCs
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 3 := by
      simp only [K]
      ring

private theorem cometric_h2_rf
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (cometricCastG0 (I := I) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) := by
  classical
  let aStar : ℕ := 2 * Module.finrank ℝ E + 10
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀0 : 0 ≤ Λ₀ :=
    mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨Λ, F, hΛ, hF, hcast⟩ :=
    cometricCastG0_order0sup_jetL2_radiusFree
      (I := I) (M := M) g aStar hδ₀ hΛ₀0
  refine ⟨F 2, hF 2, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symm_eq_self (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2 := by
    intro x
    rw [← hsymm]
    exact riemannianFiberNormSq_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  have hraw := (hcast g₁ P htie hδ_le hδ0 hδ hsup).2 2 (by
    dsimp only [aStar]
    omega)
  have h23 := covariantJetNormSq_mono (I := I) (M := M) g
    (by omega : 2 ≤ 3) P
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (cometricCastG0 (I := I) g g₁) ≤
      F 2 * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
        simpa only [covariantJetNormSq, Nat.reduceAdd] using hraw
    _ ≤ F 2 * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl h23) (hF 2)

private theorem exists_cometricCastG0_covariantJetNormSq_two_low_bound
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (cometricCastG0 (I := I) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  classical
  let aStar : ℕ := 2 * Module.finrank ℝ E + 10
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀0 : 0 ≤ Λ₀ :=
    mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨Λ, F, hΛ, hF, hcast⟩ :=
    cometricCastG0_order0sup_jetL2_radiusFree
      (I := I) (M := M) g aStar hδ₀ hΛ₀0
  refine ⟨F 2, hF 2, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symm_eq_self (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2 := by
    intro x
    rw [← hsymm]
    exact riemannianFiberNormSq_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  have hraw := (hcast g₁ P htie hδ_le hδ0 hδ hsup).2 2 (by
    dsimp only [aStar]
    omega)
  simpa only [covariantJetNormSq, Nat.reduceAdd] using hraw

private theorem exists_reindexedCometricDoubleTrace_covariantJetNormSq_two_low_bound
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (reindexedCometricDoubleTrace (I := I) (M := M) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  obtain ⟨Kc, hKc, hc⟩ :=
    exists_cometricCastG0_covariantJetNormSq_two_low_bound (I := I) (M := M) g hδ₀0 hδ₀
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := fr * Kc
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K := mul_nonneg hfr hKc
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  unfold covariantJetNormSq
  calc
    ∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 2 i
          (reindexedCometricDoubleTrace (I := I) (M := M) g g₁)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 3, fr *
        ‖iteratedCovGrad (I := I) g 3 1 i
          (cometricCastG0 (I := I) g g₁)‖ ^ 2 := by
        exact Finset.sum_le_sum fun i _ => by
          simpa only [fr] using
            norm_iteratedCovGrad_reindexedCometricDoubleTrace_sq_le (I := I) (M := M) g g₁ i
    _ = fr * covariantJetNormSq (I := I) (M := M) g 2
        (cometricCastG0 (I := I) g g₁) := by
      rw [← Finset.mul_sum]
    _ ≤ fr * (Kc *
        (1 + covariantJetNormSq (I := I) (M := M) g 2 P)) :=
      mul_le_mul_of_nonneg_left
        (hc g₁ P hP htie hδ_le hδ0 hδ) hfr
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
      simp only [K]
      ring

private theorem riemLive_h2_rf
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (reindexedCometricDoubleTrace (I := I) (M := M) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) := by
  obtain ⟨Kc, hKc, hc⟩ :=
    cometric_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := fr * Kc
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K := mul_nonneg hfr hKc
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  unfold covariantJetNormSq
  calc
    ∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 2 i
          (reindexedCometricDoubleTrace (I := I) (M := M) g g₁)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 3, fr *
        ‖iteratedCovGrad (I := I) g 3 1 i
          (cometricCastG0 (I := I) g g₁)‖ ^ 2 := by
        exact Finset.sum_le_sum fun i _ => by
          simpa only [fr] using
            norm_iteratedCovGrad_reindexedCometricDoubleTrace_sq_le (I := I) (M := M) g g₁ i
    _ = fr * covariantJetNormSq (I := I) (M := M) g 2
        (cometricCastG0 (I := I) g g₁) := by
      rw [← Finset.mul_sum]
    _ ≤ fr * (Kc *
        (1 + covariantJetNormSq (I := I) (M := M) g 3 P)) :=
      mul_le_mul_of_nonneg_left
        (hc g₁ P hP htie hδ_le hδ0 hδ) hfr
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) := by
      simp only [K]
      ring

private theorem lieCorrectionZeroRiem_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroRiemann (I := I) (M := M) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) := by
  obtain ⟨Kl, hKl, hlive⟩ :=
    riemLive_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 4 2
  let B : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (lieCorrectionZeroRiemannLift (I := I) g)
  let K : ℝ := Ca * Kl * B
  have hB : 0 ≤ B :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
      (lieCorrectionZeroRiemannLift (I := I) g)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hCa hKl) hB
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hLive := hlive g₁ P hP htie hδ_le hδ0 hδ
  have hApp := happ
    (reindexedCometricDoubleTrace (I := I) (M := M) g g₁)
    (lieCorrectionZeroRiemannLift (I := I) g)
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (lieCorrectionZeroRiemann (I := I) (M := M) g g₁) =
      covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g 2 4 2
          (reindexedCometricDoubleTrace (I := I) (M := M) g g₁)
          (lieCorrectionZeroRiemannLift (I := I) g)) := by
        rw [lieCorrectionZeroRiemann_eq_ccOperatorFieldComp (I := I) (M := M) g g₁]
        unfold covariantJetNormSq
        apply Finset.sum_congr rfl
        intro q _
        rw [iteratedCovGrad_neg, norm_neg]
    _ ≤ Ca *
        covariantJetNormSq (I := I) (M := M) g 2
          (reindexedCometricDoubleTrace (I := I) (M := M) g g₁) *
        covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroRiemannLift (I := I) g) := hApp
    _ ≤ Ca * (Kl *
        (1 + covariantJetNormSq (I := I) (M := M) g 3 P)) * B := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLive hCa) hB
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) := by
      simp only [K]
      ring

private theorem lieCorrectionZeroRiem_act_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (A : ℝ), 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (lieCorrectionZeroRiemann (I := I) (M := M) g g₁) W) ≤
        (D * (A + A ^ 2)) ^ 2 := by
  obtain ⟨K, hK, hcoeff⟩ :=
    lieCorrectionZeroRiem_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨C, hC, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 2 2
  let Z : ℝ := C * K
  let D : ℝ := Real.sqrt Z
  have hZ : 0 ≤ Z := mul_nonneg hC hK
  refine ⟨D, Real.sqrt_nonneg _, ?_⟩
  intro g₁ P W hP htie δ hδ_le hδ0 hδ A hA hP3 hW2
  have hcoeff' :
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroRiemann (I := I) (M := M) g g₁) ≤
        K * (1 + A ^ 2) := by
    exact (hcoeff g₁ P hP htie hδ_le hδ0 hδ).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hP3) hK)
  have hraw :
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (lieCorrectionZeroRiemann (I := I) (M := M) g g₁) W) ≤
        Z * (1 + A ^ 2) * A ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (lieCorrectionZeroRiemann (I := I) (M := M) g g₁) W) ≤
        C * covariantJetNormSq (I := I) (M := M) g 2
            (lieCorrectionZeroRiemann (I := I) (M := M) g g₁) *
          covariantJetNormSq (I := I) (M := M) g 2 W := by
            simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
              happ (lieCorrectionZeroRiemann (I := I) (M := M) g g₁) W
      _ ≤ C * (K * (1 + A ^ 2)) * A ^ 2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hcoeff' hC) hW2
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g W)
          (mul_nonneg hC (mul_nonneg hK (by positivity)))
      _ = Z * (1 + A ^ 2) * A ^ 2 := by
        simp only [Z]
        ring
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2
          (lieCorrectionZeroRiemann (I := I) (M := M) g g₁) W) ≤
      Z * (1 + A ^ 2) * A ^ 2 := hraw
    _ ≤ Z * (A + A ^ 2) ^ 2 := by
      have hscalar : (1 + A ^ 2) * A ^ 2 ≤ (A + A ^ 2) ^ 2 := by
        nlinarith only [sq_nonneg A, mul_nonneg hA (sq_nonneg A)]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hscalar hZ
    _ = (D * (A + A ^ 2)) ^ 2 := by
      rw [mul_pow, show D ^ 2 = Z by
        simpa only [D] using Real.sq_sqrt hZ]

private theorem mcd_h2_rf
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) := by
  classical
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀ : 0 ≤ Λ₀ := mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨F, hF, hmcd⟩ :=
    metricConnectionDifferenceLoweredCoefficient_l2_radius_free (I := I) (M := M) g g hδ₀ hΛ₀
  let K : ℝ := ∑ q ∈ Finset.range 3, F q
  have hK : 0 ≤ K := by
    exact Finset.sum_nonneg fun q _ => hF q
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symm_eq_self (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2 := by
    intro x
    rw [← hsymm]
    exact riemannianFiberNormSq_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  unfold covariantJetNormSq
  calc
    ∑ q ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 3 q
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g)‖ ^ 2 ≤
      ∑ q ∈ Finset.range 3,
        F q * (1 + ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hraw := hmcd g₁ P htie hδ_le hδ0 hδ hsup q
        have hsub : Finset.range (q + 2) ⊆ Finset.range 4 :=
          Finset.range_subset_range.mpr (by
            have : q < 3 := Finset.mem_range.mp hq
            omega)
        have hsum :
            (∑ j ∈ Finset.range (q + 2),
                ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤
              ∑ j ∈ Finset.range 4,
                ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => sq_nonneg
              ‖iteratedCovGrad (I := I) g 0 2 j P‖)
        exact le_trans hraw
          (mul_le_mul_of_nonneg_left
            (add_le_add le_rfl hsum) (hF q))
    _ = K * (1 + ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) := by
      rw [← Finset.sum_mul]

private theorem mcd_h2_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g) ≤
        (B R * A) ^ 2 := by
  obtain ⟨Bc, hBc, hconn⟩ :=
    connLower_h2_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Cc, hCc, hcorr⟩ :=
    metricLoweredConnectionDifferenceCorrection_sobolev_two_mul_bound (I := I) (M := M) hDim g
  let Z : ℝ → ℝ := fun R =>
    2 * (1 + Cc * R ^ 2) * (Bc R) ^ 2
  let B : ℝ → ℝ := fun R => Real.sqrt (Z R)
  have hZ : ∀ R : ℝ, 0 ≤ R → 0 ≤ Z R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (add_nonneg (by norm_num) (mul_nonneg hCc (sq_nonneg R))))
      (sq_nonneg (Bc R))
  refine ⟨B, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ R A hR hA hP2 hP3
  let X : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifference (I := I) (M := M) g g₁ g
  let Y : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g g₁ g P
  have hX :
      covariantJetNormSq (I := I) (M := M) g 2 X ≤
        (Bc R * A) ^ 2 := by
    rw [show X = metricLoweredConnectionDifferenceCoefficient (I := I) g g₁ from by
      simp only [X, metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc]]
    exact hconn g₁ P hP htie hδ_le hδ0 hδ
      R A hR hA hP2 hP3
  have hYraw :
      covariantJetNormSq (I := I) (M := M) g 2 Y ≤
        Cc * covariantJetNormSq (I := I) (M := M) g 2 P *
          covariantJetNormSq (I := I) (M := M) g 2 X := by
    simpa only [covariantJetNormSq, X, Y] using hcorr g₁ g P
  have hY :
      covariantJetNormSq (I := I) (M := M) g 2 Y ≤
        Cc * R ^ 2 * (Bc R * A) ^ 2 := by
    exact hYraw.trans
      (mul_le_mul
        (mul_le_mul_of_nonneg_left hP2 hCc) hX
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g X)
        (mul_nonneg hCc (sq_nonneg R)))
  have hadd := covariantJetNormSq_add_le (I := I) (M := M) g 2 X Y
  rw [metricConnectionDifferenceLoweredCoefficient_eq_lowered_add_correction (I := I) (M := M) g g₁ g P htie]
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (X + Y) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
          covariantJetNormSq (I := I) (M := M) g 2 Y) := hadd
    _ ≤ 2 * ((Bc R * A) ^ 2 +
        Cc * R ^ 2 * (Bc R * A) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ = Z R * A ^ 2 := by
      simp only [Z]
      ring
    _ = (B R * A) ^ 2 := by
      rw [mul_pow, show (B R) ^ 2 = Z R by
        simpa only [B] using Real.sq_sqrt (hZ R hR)]

private theorem connLower_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifferenceCoefficient (I := I) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 2 := by
  obtain ⟨Ko, hKo, hop⟩ :=
    exists_connectionDifferenceLowOrderOperator_covariantJetNormSq_three_radiusFree_bound (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 3 3
  let K : ℝ := Ca * Ko
  have hK : 0 ≤ K := mul_nonneg hCa hKo
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hOp : H2Poly (I := I) (M := M) g P 1 Ko
      (connectionDifferenceLowOrderOperator (I := I) (M := M) g g₁) := by
    refine ⟨hKo, ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceLowOrderOperator (I := I) (M := M) g g₁) ≤
        covariantJetNormSq (I := I) (M := M) g 3
          (connectionDifferenceLowOrderOperator (I := I) (M := M) g g₁) :=
            covariantJetNormSq_mono (I := I) (M := M) g (by omega) _
      _ ≤ Ko * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) :=
        hop g₁ P hP htie hδ_le hδ0 hδ
      _ = Ko * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 1 := by
        rw [pow_one]
  have hGrad : H2Poly (I := I) (M := M) g P 1 1
      (covGrad (I := I) (M := M) g 0 2 P) := by
    refine ⟨by norm_num, ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g 0 2 P) ≤
        covariantJetNormSq (I := I) (M := M) g 3 P :=
          grad_h2_le_h3 (I := I) (M := M) g P
      _ ≤ 1 * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 1 := by
        simp only [one_mul, pow_one]
        linarith
  have hApp :=
    hp_app_of (I := I) (M := M) g P Ca hCa
      (happ (connectionDifferenceLowOrderOperator (I := I) (M := M) g g₁)
        (covGrad (I := I) (M := M) g 0 2 P))
      hOp hGrad
  rw [← connLowOp_app (I := I) (M := M) g g₁ P hP htie]
  simpa only [K, Nat.reduceAdd, mul_one] using hApp.2

private theorem wOmega_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckVectorFieldCovector (I := I) (M := M) g g₁ g) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 3 := by
  obtain ⟨Kt, hKt, htrace⟩ :=
    trace_h2_rf (I := I) (M := M) 1 g hδ₀0 hδ₀
  obtain ⟨Kc, hKc, hconn⟩ :=
    connLower_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 3 1
  let K : ℝ := Ca * Kt * Kc
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hCa hKt) hKc
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hTr : H2Poly (I := I) (M := M) g P 1 Kt
      (reindexedPureTrace (I := I) (M := M) g g₁ 1 (Equiv.refl _)) := by
    refine ⟨hKt, ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g g₁ 1 (Equiv.refl _)) ≤
        Kt * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) :=
          htrace g₁ P hP htie hδ_le hδ0 hδ _
      _ ≤ Kt * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl
            (covariantJetNormSq_mono (I := I) (M := M) g (by omega : 2 ≤ 3) P))
          hKt
      _ = Kt * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 1 := by
        rw [pow_one]
  have hConn : H2Poly (I := I) (M := M) g P 2 Kc
      (metricLoweredConnectionDifferenceCoefficient (I := I) g g₁) :=
    ⟨hKc, hconn g₁ P hP htie hδ_le hδ0 hδ⟩
  have hApp :=
    hp_app_of (I := I) (M := M) g P Ca hCa
      (happ
        (reindexedPureTrace (I := I) (M := M) g g₁ 1 (Equiv.refl _))
        (metricLoweredConnectionDifferenceCoefficient (I := I) g g₁))
      hTr hConn
  rw [deTurckVectorFieldCovector_eq_reindexedPureTrace_ccOperatorFieldComp (I := I) (M := M) g g₁]
  simpa only [K, Nat.reduceAdd] using hApp.2

private theorem wOmega_h2_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckVectorFieldCovector (I := I) (M := M) g g₁ g) ≤
        (B R * A) ^ 2 := by
  obtain ⟨Kt, hKt, htrace⟩ :=
    trace_h2_rf (I := I) (M := M) 1 g hδ₀0 hδ₀
  obtain ⟨Bc, hBc, hconn⟩ :=
    connLower_h2_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 3 1
  let Z : ℝ → ℝ := fun R =>
    Ca * (Kt * (1 + R ^ 2)) * (Bc R) ^ 2
  let B : ℝ → ℝ := fun R => Real.sqrt (Z R)
  have hZ : ∀ R : ℝ, 0 ≤ R → 0 ≤ Z R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg hCa (mul_nonneg hKt (by positivity)))
      (sq_nonneg (Bc R))
  refine ⟨B, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ R A hR hA hP2 hP3
  have hTr :
      covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g g₁ 1 (Equiv.refl _)) ≤
        Kt * (1 + R ^ 2) :=
    (htrace g₁ P hP htie hδ_le hδ0 hδ _).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl hP2) hKt)
  have hConn :
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifferenceCoefficient (I := I) g g₁) ≤
        (Bc R * A) ^ 2 :=
    hconn g₁ P hP htie hδ_le hδ0 hδ
      R A hR hA hP2 hP3
  have hApp := happ
    (reindexedPureTrace (I := I) (M := M) g g₁ 1 (Equiv.refl _))
    (metricLoweredConnectionDifferenceCoefficient (I := I) g g₁)
  rw [deTurckVectorFieldCovector_eq_reindexedPureTrace_ccOperatorFieldComp (I := I) (M := M) g g₁]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g 0 3 1
          (reindexedPureTrace (I := I) (M := M) g g₁ 1 (Equiv.refl _))
          (metricLoweredConnectionDifferenceCoefficient (I := I) g g₁)) ≤
      Ca * covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g g₁ 1 (Equiv.refl _)) *
        covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifferenceCoefficient (I := I) g g₁) := hApp
    _ ≤ Ca * (Kt * (1 + R ^ 2)) * (Bc R * A) ^ 2 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hTr hCa) hConn
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
          (metricLoweredConnectionDifferenceCoefficient (I := I) g g₁))
        (mul_nonneg hCa (mul_nonneg hKt (by positivity)))
    _ = Z R * A ^ 2 := by
      simp only [Z]
      ring
    _ = (B R * A) ^ 2 := by
      rw [mul_pow, show (B R) ^ 2 = Z R by
        simpa only [B] using Real.sq_sqrt (hZ R hR)]

private theorem ip_h2
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ om : SmoothCcTensor g 0 1,
        covariantJetNormSq (I := I) (M := M) g 2
            (ipLowCc (I := I) (M := M) g om) ≤
          C * covariantJetNormSq (I := I) (M := M) g 2 om := by
  obtain ⟨c, hc0, hc⟩ :=
    norm_iteratedCovGrad_ipLow_le (I := I) (M := M) g
  let C : ℝ := ∑ l ∈ Finset.range 3, c l
  have hC : 0 ≤ C := Finset.sum_nonneg fun l _ => hc0 l
  refine ⟨C, hC, ?_⟩
  intro om
  unfold covariantJetNormSq
  calc
    ∑ l ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 2 1 l
          (ipLowCc (I := I) (M := M) g om)‖ ^ 2 ≤
      ∑ l ∈ Finset.range 3, c l *
        (∑ m ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 1 m om‖ ^ 2) := by
        refine Finset.sum_le_sum fun l hl => ?_
        have hraw := hc om l
        have hsub : Finset.range (l + 1) ⊆ Finset.range 3 :=
          Finset.range_subset_range.mpr (by
            have : l < 3 := Finset.mem_range.mp hl
            omega)
        have hsum :
            (∑ m ∈ Finset.range (l + 1),
                ‖iteratedCovGrad (I := I) g 0 1 m om‖ ^ 2) ≤
              ∑ m ∈ Finset.range 3,
                ‖iteratedCovGrad (I := I) g 0 1 m om‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun m _ _ => sq_nonneg
              ‖iteratedCovGrad (I := I) g 0 1 m om‖)
        exact le_trans hraw
          (mul_le_mul_of_nonneg_left hsum (hc0 l))
    _ = C * ∑ m ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 1 m om‖ ^ 2 := by
      rw [← Finset.sum_mul]

private theorem vbMcd_h2
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g₁ : SmoothRiemannianMetric I M,
        covariantJetNormSq (I := I) (M := M) g 2
            (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g g₁) ≤
          C * covariantJetNormSq (I := I) (M := M) g 2
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g) := by
  let C : ℝ := Module.finrank ℝ E
  have hC : 0 ≤ C := Nat.cast_nonneg _
  refine ⟨C, hC, ?_⟩
  intro g₁
  unfold covariantJetNormSq
  calc
    ∑ m ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 1 4 m
          (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g g₁)‖ ^ 2 ≤
      ∑ m ∈ Finset.range 3, C *
        ‖iteratedCovGrad (I := I) g 0 3 m
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g)‖ ^ 2 := by
        exact Finset.sum_le_sum fun m _ => by
          simpa only [C] using
            norm_iteratedCovGrad_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_sq_le (I := I) (M := M) g g₁ m
    _ = C * ∑ m ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 3 m
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g)‖ ^ 2 := by
      rw [← Finset.mul_sum]

private theorem lieCorrectionZeroVB_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundle (I := I) (M := M) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 5 := by
  obtain ⟨Kl, hKl, hlive⟩ :=
    riemLive_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Km, hKm, hmcd⟩ :=
    mcd_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Ko, hKo, homega⟩ :=
    wOmega_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Cv, hCv, hvb⟩ := vbMcd_h2 (I := I) (M := M) g
  obtain ⟨Ci, hCi, hip⟩ := ip_h2 (I := I) (M := M) g
  obtain ⟨Ca, hCa, happA⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 1 4
  obtain ⟨Cb, hCb, happB⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 4 2
  let Kvm : ℝ := Cv * Km
  let Kip : ℝ := Ci * Ko
  let Kinner : ℝ := Ca * Kvm * Kip
  let Kouter : ℝ := Cb * Kl * Kinner
  let K : ℝ := (2 : ℝ) ^ 2 * Kouter
  have hKvm : 0 ≤ Kvm := mul_nonneg hCv hKm
  have hKip : 0 ≤ Kip := mul_nonneg hCi hKo
  have hKinner : 0 ≤ Kinner :=
    mul_nonneg (mul_nonneg hCa hKvm) hKip
  have hKouter : 0 ≤ Kouter :=
    mul_nonneg (mul_nonneg hCb hKl) hKinner
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) hKouter
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hLive : H2Poly (I := I) (M := M) g P 1 Kl
      (reindexedCometricDoubleTrace (I := I) (M := M) g g₁) :=
    ⟨hKl, by
      simpa only [pow_one] using
        hlive g₁ P hP htie hδ_le hδ0 hδ⟩
  have hMcd : H2Poly (I := I) (M := M) g P 1 Km
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g) :=
    ⟨hKm, by
      simpa only [pow_one] using
        hmcd g₁ P hP htie hδ_le hδ0 hδ⟩
  have hVBArm : H2Poly (I := I) (M := M) g P 1 Kvm
      (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g g₁) := by
    refine ⟨hKvm, ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g g₁) ≤
        Cv * covariantJetNormSq (I := I) (M := M) g 2
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g) :=
            hvb g₁
      _ ≤ Cv * (Km *
          (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 1) :=
        mul_le_mul_of_nonneg_left hMcd.2 hCv
      _ = Kvm * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 1 := by
        simp only [Kvm]
        ring
  have hOmega : H2Poly (I := I) (M := M) g P 3 Ko
      (deTurckVectorFieldCovector (I := I) (M := M) g g₁ g) :=
    ⟨hKo, homega g₁ P hP htie hδ_le hδ0 hδ⟩
  have hIp : H2Poly (I := I) (M := M) g P 3 Kip
      (ipLowCc (I := I) (M := M) g
        (deTurckVectorFieldCovector (I := I) (M := M) g g₁ g)) := by
    refine ⟨hKip, ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (ipLowCc (I := I) (M := M) g
            (deTurckVectorFieldCovector (I := I) (M := M) g g₁ g)) ≤
        Ci * covariantJetNormSq (I := I) (M := M) g 2
          (deTurckVectorFieldCovector (I := I) (M := M) g g₁ g) := hip _
      _ ≤ Ci * (Ko *
          (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 3) :=
        mul_le_mul_of_nonneg_left hOmega.2 hCi
      _ = Kip * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 3 := by
        simp only [Kip]
        ring
  have hInner :=
    hp_app_of (I := I) (M := M) g P Ca hCa
      (happA (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g g₁)
        (ipLowCc (I := I) (M := M) g
          (deTurckVectorFieldCovector (I := I) (M := M) g g₁ g)))
      hVBArm hIp
  have hOuter :=
    hp_app_of (I := I) (M := M) g P Cb hCb
      (happB (reindexedCometricDoubleTrace (I := I) (M := M) g g₁)
        (ccOperatorFieldComp (I := I) (M := M) g 2 1 4
          (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g g₁)
          (ipLowCc (I := I) (M := M) g
            (deTurckVectorFieldCovector (I := I) (M := M) g g₁ g))))
      hLive hInner
  have hScaled :=
    hp_smul (I := I) (M := M) g P (2 : ℝ) hOuter
  rw [lieCorrectionZeroVectorBundle_eq_expansion (I := I) (M := M) g g₁]
  simpa only [lieCorrectionZeroVectorBundleExpansion, Kvm, Kip, Kinner, Kouter, K,
    Nat.reduceAdd] using hScaled.2

private theorem lieCorrectionZeroVB_h2_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundle (I := I) (M := M) g g₁) ≤
        (D R * A ^ 2) ^ 2 := by
  obtain ⟨Kl, hKl, hlive⟩ :=
    exists_reindexedCometricDoubleTrace_covariantJetNormSq_two_low_bound (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Bm, hBm, hmcd⟩ :=
    mcd_h2_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Bo, hBo, homega⟩ :=
    wOmega_h2_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Cv, hCv, hvb⟩ := vbMcd_h2 (I := I) (M := M) g
  obtain ⟨Ci, hCi, hip⟩ := ip_h2 (I := I) (M := M) g
  obtain ⟨Ca, hCa, happA⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 1 4
  obtain ⟨Cb, hCb, happB⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 4 2
  let Z : ℝ → ℝ := fun R =>
    (2 : ℝ) ^ 2 *
      (Cb * (Kl * (1 + R ^ 2)) *
        (Ca * (Cv * (Bm R) ^ 2) * (Ci * (Bo R) ^ 2)))
  let D : ℝ → ℝ := fun R => Real.sqrt (Z R)
  have hZ : ∀ R : ℝ, 0 ≤ R → 0 ≤ Z R := by
    intro R hR
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg
        (mul_nonneg hCb (mul_nonneg hKl (by positivity)))
        (mul_nonneg
          (mul_nonneg hCa (mul_nonneg hCv (sq_nonneg (Bm R))))
          (mul_nonneg hCi (sq_nonneg (Bo R)))))
  refine ⟨D, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ R A hR hA hP2 hP3
  let L : ℝ := Kl * (1 + R ^ 2)
  let VM : ℝ := Cv * (Bm R) ^ 2
  let IP : ℝ := Ci * (Bo R) ^ 2
  have hL : 0 ≤ L := mul_nonneg hKl (by positivity)
  have hVM : 0 ≤ VM := mul_nonneg hCv (sq_nonneg _)
  have hIP : 0 ≤ IP := mul_nonneg hCi (sq_nonneg _)
  have hLive : H2Poly (I := I) (M := M) g P 0 L
      (reindexedCometricDoubleTrace (I := I) (M := M) g g₁) := by
    refine ⟨hL, ?_⟩
    simpa only [H2Poly, pow_zero, mul_one, L] using
      (hlive g₁ P hP htie hδ_le hδ0 hδ).trans
        (mul_le_mul_of_nonneg_left
          (add_le_add le_rfl hP2) hKl)
  have hMcd : H2Poly (I := I) (M := M) g P 0
      ((Bm R * A) ^ 2)
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g) := by
    refine ⟨sq_nonneg _, ?_⟩
    simpa only [H2Poly, pow_zero, mul_one] using
      hmcd g₁ P hP htie hδ_le hδ0 hδ
        R A hR hA hP2 hP3
  have hVBArm : H2Poly (I := I) (M := M) g P 0
      (VM * A ^ 2)
      (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g g₁) := by
    refine ⟨mul_nonneg hVM (sq_nonneg A), ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g g₁) ≤
        Cv * covariantJetNormSq (I := I) (M := M) g 2
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g) :=
        hvb g₁
      _ ≤ Cv * (Bm R * A) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (by simpa only [pow_zero, mul_one] using hMcd.2) hCv
      _ = (VM * A ^ 2) *
          (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 0 := by
        simp only [VM, pow_zero, mul_one]
        ring
  have hOmega : H2Poly (I := I) (M := M) g P 0
      ((Bo R * A) ^ 2)
      (deTurckVectorFieldCovector (I := I) (M := M) g g₁ g) := by
    refine ⟨sq_nonneg _, ?_⟩
    simpa only [H2Poly, pow_zero, mul_one] using
      homega g₁ P hP htie hδ_le hδ0 hδ
        R A hR hA hP2 hP3
  have hIp : H2Poly (I := I) (M := M) g P 0
      (IP * A ^ 2)
      (ipLowCc (I := I) (M := M) g
        (deTurckVectorFieldCovector (I := I) (M := M) g g₁ g)) := by
    refine ⟨mul_nonneg hIP (sq_nonneg A), ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (ipLowCc (I := I) (M := M) g
            (deTurckVectorFieldCovector (I := I) (M := M) g g₁ g)) ≤
        Ci * covariantJetNormSq (I := I) (M := M) g 2
          (deTurckVectorFieldCovector (I := I) (M := M) g g₁ g) := hip _
      _ ≤ Ci * (Bo R * A) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (by simpa only [pow_zero, mul_one] using hOmega.2) hCi
      _ = (IP * A ^ 2) *
          (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 0 := by
        simp only [IP, pow_zero, mul_one]
        ring
  have hInner :=
    hp_app_of (I := I) (M := M) g P Ca hCa
      (happA (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g g₁)
        (ipLowCc (I := I) (M := M) g
          (deTurckVectorFieldCovector (I := I) (M := M) g g₁ g)))
      hVBArm hIp
  have hOuter :=
    hp_app_of (I := I) (M := M) g P Cb hCb
      (happB (reindexedCometricDoubleTrace (I := I) (M := M) g g₁)
        (ccOperatorFieldComp (I := I) (M := M) g 2 1 4
          (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g g₁)
          (ipLowCc (I := I) (M := M) g
            (deTurckVectorFieldCovector (I := I) (M := M) g g₁ g))))
      hLive hInner
  have hScaled :=
    hp_smul (I := I) (M := M) g P (2 : ℝ) hOuter
  rw [lieCorrectionZeroVectorBundle_eq_expansion (I := I) (M := M) g g₁]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (lieCorrectionZeroVectorBundleExpansion (I := I) (M := M) g g₁) ≤
      (2 : ℝ) ^ 2 *
        (Cb * L * (Ca * (VM * A ^ 2) * (IP * A ^ 2))) := by
          simpa only [lieCorrectionZeroVectorBundleExpansion, Nat.zero_add, pow_zero, mul_one]
            using hScaled.2
    _ = Z R * A ^ 4 := by
      simp only [Z, L, VM, IP]
      ring
    _ = (D R * A ^ 2) ^ 2 := by
      rw [mul_pow, show (D R) ^ 2 = Z R by
        simpa only [D] using Real.sq_sqrt (hZ R hR)]
      ring

private theorem lieCorrectionZeroVB_act_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (lieCorrectionZeroVectorBundle (I := I) (M := M) g g₁) W) ≤
        (D R * A ^ 2) ^ 2 := by
  obtain ⟨Bv, hBv, hv⟩ :=
    lieCorrectionZeroVB_h2_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_quad (I := I) (M := M) hDim g
  let D : ℝ → ℝ := fun R => Ca * Bv R * R
  refine ⟨D, fun R hR =>
    mul_nonneg (mul_nonneg hCa (hBv R hR)) hR, ?_⟩
  intro g₁ P W hP htie δ hδ_le hδ0 hδ
    R A hR hA hP2 hP3 hW2
  have hcoeff :=
    hv g₁ P hP htie hδ_le hδ0 hδ
      R A hR hA hP2 hP3
  have hraw := happ
    (lieCorrectionZeroVectorBundle (I := I) (M := M) g g₁) W
    (Bv R) R A (hBv R hR) hR hA hcoeff hW2
  simpa only [D, mul_assoc] using hraw

private theorem lieCorrectionZeroMixedConnection_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroMixedConnection (I := I) (M := M) g g₁ g) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 5 := by
  obtain ⟨Km, hKm, hmcd⟩ :=
    mcd_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨K2, hK2, ht2⟩ :=
    trace_h2_rf (I := I) (M := M) 2 g hδ₀0 hδ₀
  obtain ⟨K3, hK3, ht3⟩ :=
    trace_h2_rf (I := I) (M := M) 3 g hδ₀0 hδ₀
  obtain ⟨K4, hK4, ht4⟩ :=
    trace_h2_rf (I := I) (M := M) 4 g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happA⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 5 3
  obtain ⟨Cb, hCb, happB⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 3 6
  obtain ⟨Cc, hCc, happC⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 6 4
  obtain ⟨Cd, hCd, happD⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 4 2
  let fr : ℝ := Module.finrank ℝ E
  let Ks2 : ℝ := fr * (fr * Km)
  let Ks3 : ℝ := fr * (fr * (fr * Km))
  let Ktail : ℝ := Ca * K3 * Ks2
  let Kmid : ℝ := Cb * Ks3 * Ktail
  let Ktraced : ℝ := Cc * K4 * Kmid
  let Khalf : ℝ := Cd * K2 * Ktraced
  let Ksum : ℝ := 2 * (Khalf + Khalf)
  let K : ℝ := (2 : ℝ) ^ 2 * Ksum
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hKs2 : 0 ≤ Ks2 := mul_nonneg hfr (mul_nonneg hfr hKm)
  have hKs3 : 0 ≤ Ks3 :=
    mul_nonneg hfr (mul_nonneg hfr (mul_nonneg hfr hKm))
  have hKtail : 0 ≤ Ktail :=
    mul_nonneg (mul_nonneg hCa hK3) hKs2
  have hKmid : 0 ≤ Kmid :=
    mul_nonneg (mul_nonneg hCb hKs3) hKtail
  have hKtraced : 0 ≤ Ktraced :=
    mul_nonneg (mul_nonneg hCc hK4) hKmid
  have hKhalf : 0 ≤ Khalf :=
    mul_nonneg (mul_nonneg hCd hK2) hKtraced
  have hKsum : 0 ≤ Ksum :=
    mul_nonneg (by norm_num) (add_nonneg hKhalf hKhalf)
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) hKsum
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hMcd : H2Poly (I := I) (M := M) g P 1 Km
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g) :=
    ⟨hKm, by
      simpa only [pow_one] using
        hmcd g₁ P hP htie hδ_le hδ0 hδ⟩
  have hT2 (σ : Equiv.Perm (Fin 4)) :
      H2Poly (I := I) (M := M) g P 1 K2
        (reindexedPureTrace (I := I) (M := M) g g₁ 2 σ) := by
    refine ⟨hK2, ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g g₁ 2 σ) ≤
        K2 * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) :=
          ht2 g₁ P hP htie hδ_le hδ0 hδ σ
      _ ≤ K2 * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl
            (covariantJetNormSq_mono (I := I) (M := M) g (by omega : 2 ≤ 3) P))
          hK2
      _ = K2 * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 1 := by
        rw [pow_one]
  have hT3 : H2Poly (I := I) (M := M) g P 1 K3
      (reindexedPureTrace (I := I) (M := M) g g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) := by
    refine ⟨hK3, ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) ≤
        K3 * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) :=
          ht3 g₁ P hP htie hδ_le hδ0 hδ _
      _ ≤ K3 * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl
            (covariantJetNormSq_mono (I := I) (M := M) g (by omega : 2 ≤ 3) P))
          hK3
      _ = K3 * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 1 := by
        rw [pow_one]
  have hT4 : H2Poly (I := I) (M := M) g P 1 K4
      (reindexedPureTrace (I := I) (M := M) g g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) := by
    refine ⟨hK4, ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) ≤
        K4 * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) :=
          ht4 g₁ P hP htie hδ_le hδ0 hδ _
      _ ≤ K4 * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl
            (covariantJetNormSq_mono (I := I) (M := M) g (by omega : 2 ≤ 3) P))
          hK4
      _ = K4 * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 1 := by
        rw [pow_one]
  have hS2 : H2Poly (I := I) (M := M) g P 1 Ks2
      (slotExtendIter (I := I) (M := M) g 0 3 2
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g)) := by
    simpa only [Ks2, fr] using
      hp_slot2 (I := I) (M := M) g P hMcd
  have hS3 : H2Poly (I := I) (M := M) g P 1 Ks3
      (slotExtendIter (I := I) (M := M) g 0 3 3
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g)) := by
    simpa only [Ks3, fr] using
      hp_slot3 (I := I) (M := M) g P hMcd
  have hHalf (σ : Equiv.Perm (Fin 4)) :
      H2Poly (I := I) (M := M) g P 5 Khalf
        (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g g₁ g σ) := by
    have hTail :=
      hp_app_of (I := I) (M := M) g P Ca hCa
        (happA
          (reindexedPureTrace (I := I) (M := M) g g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
          (slotExtendIter (I := I) (M := M) g 0 3 2
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g)))
        hT3 hS2
    have hMid :=
      hp_app_of (I := I) (M := M) g P Cb hCb
        (happB
          (slotExtendIter (I := I) (M := M) g 0 3 3
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g))
          (ccOperatorFieldComp (I := I) (M := M) g 2 5 3
            (reindexedPureTrace (I := I) (M := M) g g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
            (slotExtendIter (I := I) (M := M) g 0 3 2
              (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g))))
        hS3 hTail
    have hTraced :=
      hp_app_of (I := I) (M := M) g P Cc hCc
        (happC
          (reindexedPureTrace (I := I) (M := M) g g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne)
          (ccOperatorFieldComp (I := I) (M := M) g 2 3 6
            (slotExtendIter (I := I) (M := M) g 0 3 3
              (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g))
            (ccOperatorFieldComp (I := I) (M := M) g 2 5 3
              (reindexedPureTrace (I := I) (M := M) g g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
              (slotExtendIter (I := I) (M := M) g 0 3 2
                (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g)))))
        hT4 hMid
    have hLast :=
      hp_app_of (I := I) (M := M) g P Cd hCd
        (happD
          (reindexedPureTrace (I := I) (M := M) g g₁ 2 σ)
          (ccOperatorFieldComp (I := I) (M := M) g 2 6 4
            (reindexedPureTrace (I := I) (M := M) g g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne)
            (ccOperatorFieldComp (I := I) (M := M) g 2 3 6
              (slotExtendIter (I := I) (M := M) g 0 3 3
                (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g))
              (ccOperatorFieldComp (I := I) (M := M) g 2 5 3
                (reindexedPureTrace (I := I) (M := M) g g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
                (slotExtendIter (I := I) (M := M) g 0 3 2
                  (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g))))))
        (hT2 σ) hTraced
    simpa only [lieCorrectionZeroMixedConnectionHalfExpansion, Ktail, Kmid, Ktraced, Khalf,
      Nat.reduceAdd] using hLast
  have hSum :=
    hp_add (I := I) (M := M) g P
      (hHalf lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
      (hHalf (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))
  have hScaled :=
    hp_smul (I := I) (M := M) g P (2 : ℝ) hSum
  rw [lieCorrectionZeroMixedConnection_eq_expansion (I := I) (M := M) g g₁ g]
  simpa only [lieCorrectionZeroMixedConnectionExpansion, Ksum, K, Nat.reduceAdd] using hScaled.2

private theorem lieCorrectionZeroMixedConnection_h2_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroMixedConnection (I := I) (M := M) g g₁ g) ≤
        (D R * A ^ 2) ^ 2 := by
  obtain ⟨Bm, hBm, hmcd⟩ :=
    mcd_h2_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨K2, hK2, ht2⟩ :=
    trace_h2_rf (I := I) (M := M) 2 g hδ₀0 hδ₀
  obtain ⟨K3, hK3, ht3⟩ :=
    trace_h2_rf (I := I) (M := M) 3 g hδ₀0 hδ₀
  obtain ⟨K4, hK4, ht4⟩ :=
    trace_h2_rf (I := I) (M := M) 4 g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happA⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 5 3
  obtain ⟨Cb, hCb, happB⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 3 6
  obtain ⟨Cc, hCc, happC⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 6 4
  obtain ⟨Cd, hCd, happD⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 4 2
  let fr : ℝ := Module.finrank ℝ E
  let M0 : ℝ → ℝ := fun R => (Bm R) ^ 2
  let T2 : ℝ → ℝ := fun R => K2 * (1 + R ^ 2)
  let T3 : ℝ → ℝ := fun R => K3 * (1 + R ^ 2)
  let T4 : ℝ → ℝ := fun R => K4 * (1 + R ^ 2)
  let S2 : ℝ → ℝ := fun R => fr * (fr * M0 R)
  let S3 : ℝ → ℝ := fun R => fr * (fr * (fr * M0 R))
  let Ktail : ℝ → ℝ := fun R => Ca * T3 R * S2 R
  let Kmid : ℝ → ℝ := fun R => Cb * S3 R * Ktail R
  let Ktraced : ℝ → ℝ := fun R => Cc * T4 R * Kmid R
  let Khalf : ℝ → ℝ := fun R => Cd * T2 R * Ktraced R
  let Ksum : ℝ → ℝ := fun R => 2 * (Khalf R + Khalf R)
  let Z : ℝ → ℝ := fun R => (2 : ℝ) ^ 2 * Ksum R
  let D : ℝ → ℝ := fun R => Real.sqrt (Z R)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hM0 : ∀ R, 0 ≤ M0 R := fun R => sq_nonneg _
  have hT2 : ∀ R, 0 ≤ T2 R :=
    fun R => mul_nonneg hK2 (by positivity)
  have hT3 : ∀ R, 0 ≤ T3 R :=
    fun R => mul_nonneg hK3 (by positivity)
  have hT4 : ∀ R, 0 ≤ T4 R :=
    fun R => mul_nonneg hK4 (by positivity)
  have hS2 : ∀ R, 0 ≤ S2 R :=
    fun R => mul_nonneg hfr (mul_nonneg hfr (hM0 R))
  have hS3 : ∀ R, 0 ≤ S3 R :=
    fun R => mul_nonneg hfr
      (mul_nonneg hfr (mul_nonneg hfr (hM0 R)))
  have hKtail : ∀ R, 0 ≤ Ktail R :=
    fun R => mul_nonneg (mul_nonneg hCa (hT3 R)) (hS2 R)
  have hKmid : ∀ R, 0 ≤ Kmid R :=
    fun R => mul_nonneg (mul_nonneg hCb (hS3 R)) (hKtail R)
  have hKtraced : ∀ R, 0 ≤ Ktraced R :=
    fun R => mul_nonneg (mul_nonneg hCc (hT4 R)) (hKmid R)
  have hKhalf : ∀ R, 0 ≤ Khalf R :=
    fun R => mul_nonneg (mul_nonneg hCd (hT2 R)) (hKtraced R)
  have hKsum : ∀ R, 0 ≤ Ksum R :=
    fun R => mul_nonneg (by norm_num)
      (add_nonneg (hKhalf R) (hKhalf R))
  have hZ : ∀ R, 0 ≤ Z R :=
    fun R => mul_nonneg (sq_nonneg _) (hKsum R)
  refine ⟨D, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ R A hR hA hP2 hP3
  have hMcd : H2Poly (I := I) (M := M) g P 0
      (M0 R * A ^ 2)
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g) := by
    refine ⟨mul_nonneg (hM0 R) (sq_nonneg A), ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g) ≤
        (Bm R * A) ^ 2 :=
          hmcd g₁ P hP htie hδ_le hδ0 hδ
            R A hR hA hP2 hP3
      _ = (M0 R * A ^ 2) *
          (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 0 := by
        simp only [M0, pow_zero, mul_one]
        ring
  have hTrace (p : ℕ) (K : ℝ)
      (T : SmoothCcTensor g (p + 2) p)
      (hK : 0 ≤ K)
      (hraw : covariantJetNormSq (I := I) (M := M) g 2 T ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P)) :
      H2Poly (I := I) (M := M) g P 0
        (K * (1 + R ^ 2)) T := by
    refine ⟨mul_nonneg hK (by positivity), ?_⟩
    exact hraw.trans
      (by
        simpa only [pow_zero, mul_one] using
          mul_le_mul_of_nonneg_left
            (add_le_add le_rfl hP2) hK)
  have hT2p (σ : Equiv.Perm (Fin 4)) :
      H2Poly (I := I) (M := M) g P 0 (T2 R)
        (reindexedPureTrace (I := I) (M := M) g g₁ 2 σ) := by
    simpa only [T2] using hTrace 2 K2
      (reindexedPureTrace (I := I) (M := M) g g₁ 2 σ) hK2
      (ht2 g₁ P hP htie hδ_le hδ0 hδ σ)
  have hT3p :
      H2Poly (I := I) (M := M) g P 0 (T3 R)
        (reindexedPureTrace (I := I) (M := M) g g₁ 3
          lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) := by
    simpa only [T3] using hTrace 3 K3
      (reindexedPureTrace (I := I) (M := M) g g₁ 3
        lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) hK3
      (ht3 g₁ P hP htie hδ_le hδ0 hδ _)
  have hT4p :
      H2Poly (I := I) (M := M) g P 0 (T4 R)
        (reindexedPureTrace (I := I) (M := M) g g₁ 4
          lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) := by
    simpa only [T4] using hTrace 4 K4
      (reindexedPureTrace (I := I) (M := M) g g₁ 4
        lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) hK4
      (ht4 g₁ P hP htie hδ_le hδ0 hδ _)
  have hS2raw :=
    hp_slot2 (I := I) (M := M) g P hMcd
  have hS2p : H2Poly (I := I) (M := M) g P 0
      (S2 R * A ^ 2)
      (slotExtendIter (I := I) (M := M) g 0 3 2
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g)) := by
    have heq :
        fr * (fr * (M0 R * A ^ 2)) = S2 R * A ^ 2 := by
      simp only [S2]
      ring
    rw [← heq]
    simpa only [fr] using hS2raw
  have hS3raw :=
    hp_slot3 (I := I) (M := M) g P hMcd
  have hS3p : H2Poly (I := I) (M := M) g P 0
      (S3 R * A ^ 2)
      (slotExtendIter (I := I) (M := M) g 0 3 3
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g)) := by
    have heq :
        fr * (fr * (fr * (M0 R * A ^ 2))) =
          S3 R * A ^ 2 := by
      simp only [S3]
      ring
    rw [← heq]
    simpa only [fr] using hS3raw
  have hHalf (σ : Equiv.Perm (Fin 4)) :
      H2Poly (I := I) (M := M) g P 0
        (Khalf R * A ^ 4)
        (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g g₁ g σ) := by
    have hTailRaw :=
      hp_app_of (I := I) (M := M) g P Ca hCa
        (happA
          (reindexedPureTrace (I := I) (M := M) g g₁ 3
            lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
          (slotExtendIter (I := I) (M := M) g 0 3 2
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g)))
        hT3p hS2p
    have hTail : H2Poly (I := I) (M := M) g P 0
        (Ktail R * A ^ 2)
        (ccOperatorFieldComp (I := I) (M := M) g 2 5 3
          (reindexedPureTrace (I := I) (M := M) g g₁ 3
            lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
          (slotExtendIter (I := I) (M := M) g 0 3 2
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g))) := by
      have heq :
          Ca * T3 R * (S2 R * A ^ 2) =
            Ktail R * A ^ 2 := by
        simp only [Ktail]
        ring
      rw [← heq]
      exact hTailRaw
    have hMidRaw :=
      hp_app_of (I := I) (M := M) g P Cb hCb
        (happB
          (slotExtendIter (I := I) (M := M) g 0 3 3
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g))
          (ccOperatorFieldComp (I := I) (M := M) g 2 5 3
            (reindexedPureTrace (I := I) (M := M) g g₁ 3
              lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
            (slotExtendIter (I := I) (M := M) g 0 3 2
              (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g))))
        hS3p hTail
    have hMid : H2Poly (I := I) (M := M) g P 0
        (Kmid R * A ^ 4)
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 6
          (slotExtendIter (I := I) (M := M) g 0 3 3
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g))
          (ccOperatorFieldComp (I := I) (M := M) g 2 5 3
            (reindexedPureTrace (I := I) (M := M) g g₁ 3
              lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
            (slotExtendIter (I := I) (M := M) g 0 3 2
              (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g)))) := by
      have heq :
          Cb * (S3 R * A ^ 2) * (Ktail R * A ^ 2) =
            Kmid R * A ^ 4 := by
        simp only [Kmid]
        ring
      rw [← heq]
      exact hMidRaw
    have hTracedRaw :=
      hp_app_of (I := I) (M := M) g P Cc hCc
        (happC
          (reindexedPureTrace (I := I) (M := M) g g₁ 4
            lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne)
          (ccOperatorFieldComp (I := I) (M := M) g 2 3 6
            (slotExtendIter (I := I) (M := M) g 0 3 3
              (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g))
            (ccOperatorFieldComp (I := I) (M := M) g 2 5 3
              (reindexedPureTrace (I := I) (M := M) g g₁ 3
                lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
              (slotExtendIter (I := I) (M := M) g 0 3 2
                (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g)))))
        hT4p hMid
    have hTraced : H2Poly (I := I) (M := M) g P 0
        (Ktraced R * A ^ 4)
        (ccOperatorFieldComp (I := I) (M := M) g 2 6 4
          (reindexedPureTrace (I := I) (M := M) g g₁ 4
            lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne)
          (ccOperatorFieldComp (I := I) (M := M) g 2 3 6
            (slotExtendIter (I := I) (M := M) g 0 3 3
              (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g))
            (ccOperatorFieldComp (I := I) (M := M) g 2 5 3
              (reindexedPureTrace (I := I) (M := M) g g₁ 3
                lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
              (slotExtendIter (I := I) (M := M) g 0 3 2
                (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g))))) := by
      have heq :
          Cc * T4 R * (Kmid R * A ^ 4) =
            Ktraced R * A ^ 4 := by
        simp only [Ktraced]
        ring
      rw [← heq]
      exact hTracedRaw
    have hLastRaw :=
      hp_app_of (I := I) (M := M) g P Cd hCd
        (happD
          (reindexedPureTrace (I := I) (M := M) g g₁ 2 σ)
          (ccOperatorFieldComp (I := I) (M := M) g 2 6 4
            (reindexedPureTrace (I := I) (M := M) g g₁ 4
              lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne)
            (ccOperatorFieldComp (I := I) (M := M) g 2 3 6
              (slotExtendIter (I := I) (M := M) g 0 3 3
                (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g))
              (ccOperatorFieldComp (I := I) (M := M) g 2 5 3
                (reindexedPureTrace (I := I) (M := M) g g₁ 3
                  lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
                (slotExtendIter (I := I) (M := M) g 0 3 2
                  (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g))))))
        (hT2p σ) hTraced
    have heq :
        Cd * T2 R * (Ktraced R * A ^ 4) =
          Khalf R * A ^ 4 := by
      simp only [Khalf]
      ring
    rw [← heq]
    simpa only [lieCorrectionZeroMixedConnectionHalfExpansion, Nat.zero_add] using hLastRaw
  have hSumRaw :=
    hp_add (I := I) (M := M) g P
      (hHalf lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
      (hHalf (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))
  have hSumP : H2Poly (I := I) (M := M) g P 0
      (Ksum R * A ^ 4)
      (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g g₁ g lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne +
        lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g g₁ g
          (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)) := by
    have heq :
        2 * (Khalf R * A ^ 4 + Khalf R * A ^ 4) =
          Ksum R * A ^ 4 := by
      simp only [Ksum]
      ring
    rw [← heq]
    exact hSumRaw
  have hScaledRaw :=
    hp_smul (I := I) (M := M) g P (2 : ℝ) hSumP
  have hScaled : H2Poly (I := I) (M := M) g P 0
      (Z R * A ^ 4)
      ((2 : ℝ) •
        (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g g₁ g lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne +
          lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g g₁ g
            (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))) := by
    have heq :
        (2 : ℝ) ^ 2 * (Ksum R * A ^ 4) =
          Z R * A ^ 4 := by
      simp only [Z]
      ring
    rw [← heq]
    exact hScaledRaw
  rw [lieCorrectionZeroMixedConnection_eq_expansion (I := I) (M := M) g g₁ g]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (lieCorrectionZeroMixedConnectionExpansion (I := I) (M := M) g g₁ g) ≤
      Z R * A ^ 4 := by
        simpa only [lieCorrectionZeroMixedConnectionExpansion, pow_zero, mul_one] using hScaled.2
    _ = (D R * A ^ 2) ^ 2 := by
      rw [mul_pow, show (D R) ^ 2 = Z R by
        simpa only [D] using Real.sq_sqrt (hZ R)]
      ring

private theorem lieCorrectionZeroMixedConnection_act_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (lieCorrectionZeroMixedConnection (I := I) (M := M) g g₁ g) W) ≤
        (D R * A ^ 2) ^ 2 := by
  obtain ⟨Ba, hBa, ha⟩ :=
    lieCorrectionZeroMixedConnection_h2_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_quad (I := I) (M := M) hDim g
  let D : ℝ → ℝ := fun R => Ca * Ba R * R
  refine ⟨D, fun R hR =>
    mul_nonneg (mul_nonneg hCa (hBa R hR)) hR, ?_⟩
  intro g₁ P W hP htie δ hδ_le hδ0 hδ
    R A hR hA hP2 hP3 hW2
  have hcoeff :=
    ha g₁ P hP htie hδ_le hδ0 hδ
      R A hR hA hP2 hP3
  have hraw := happ
    (lieCorrectionZeroMixedConnection (I := I) (M := M) g g₁ g) W
    (Ba R) R A (hBa R hR) hR hA hcoeff hW2
  simpa only [D, mul_assoc] using hraw

private def lcvSigma1 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![0, 5, 2, 1, 3, 4] : Fin 6 → Fin 6) i,
   fun i => (![0, 3, 2, 4, 5, 1] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

private def lcvSigma2 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![4, 0, 2, 1, 3, 5] : Fin 6 → Fin 6) i,
   fun i => (![1, 3, 2, 4, 0, 5] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

private def lcvRiem1
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 6 4
    (DeTurck.cometricDoubleTraceField (I := I) g 4)
    (rsDomDomCongrSection (I := I) (M := M) g 2 6 lcvSigma1
      (slotExtendIter (I := I) (M := M) g 0 4 2
        (riemannLoweredCc (I := I) (M := M) g g g)))

private def lcvRiem2
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 6 4
    (DeTurck.cometricDoubleTraceField (I := I) g 4)
    (rsDomDomCongrSection (I := I) (M := M) g 2 6 lcvSigma2
      (slotExtendIter (I := I) (M := M) g 0 4 2
        (riemannLoweredCc (I := I) (M := M) g g g)))

private def lcvCurv
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 0 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 0 2 4 (lcvRiem1 (I := I) (M := M) g) T +
    ccOperatorFieldComp (I := I) (M := M) g 0 2 4
      (lcvRiem2 (I := I) (M := M) g) T

private def lcvOmega
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 0 3 :=
  ccOperatorFieldComp (I := I) (M := M) g 0 3 3
    (slotInsertEndoCc (I := I) (M := M) g 2
      (metricComparisonEndomorphismField (I := I) (M := M) gm g))
    (domDomCongrSection (I := I) g (finRotate 3)
      (metricLoweredConnectionDifferenceCoefficient (I := I) g gm))

private def lcvQB
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 0 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 0 3 4
    (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gm)
    (lcvOmega (I := I) (M := M) g gm)

private def lcvQA
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 0 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 0 3 4
    (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gm)
    (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1)
      (lcvOmega (I := I) (M := M) g gm))

private def lcvPermA : Equiv.Perm (Fin 4) :=
  ⟨fun i => (![2, 0, 1, 3] : Fin 4 → Fin 4) i,
   fun i => (![1, 2, 0, 3] : Fin 4 → Fin 4) i,
   by decide, by decide⟩

private def lcvPermB : Equiv.Perm (Fin 4) :=
  ⟨fun i => (![3, 0, 1, 2] : Fin 4 → Fin 4) i,
   fun i => (![1, 2, 3, 0] : Fin 4 → Fin 4) i,
   by decide, by decide⟩

private def lcvPermC : Equiv.Perm (Fin 4) :=
  ⟨fun i => (![3, 1, 0, 2] : Fin 4 → Fin 4) i,
   fun i => (![2, 1, 3, 0] : Fin 4 → Fin 4) i,
   by decide, by decide⟩

private def lcvQuad
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 0 4 :=
  domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1)
      (lcvQB (I := I) (M := M) g gm) +
    lcvQB (I := I) (M := M) g gm +
    domDomCongrSection (I := I) g lcvPermA
      (lcvQA (I := I) (M := M) g gm) +
    domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2)
      (lcvQA (I := I) (M := M) g gm) +
    domDomCongrSection (I := I) g lcvPermB
      (lcvQA (I := I) (M := M) g gm) +
    domDomCongrSection (I := I) g lcvPermC
      (lcvQA (I := I) (M := M) g gm)

private def lcvR4
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 0 4 :=
  (-(s / 2) : ℝ) • lcvCurv (I := I) (M := M) g T -
    lcvQuad (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hδ hδZ s)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem lcvR4_eq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδ hδZ s =
      lcvR4 (I := I) (M := M) g T hδ hδZ s := by
  rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem lcvPair_eq
    (g gm : SmoothRiemannianMetric I M) :
    cometricDoublePairTraceCoefficient (I := I) (M := M) g gm =
      ccOperatorFieldComp (I := I) (M := M) g 6 4 2
        (pureTrace (I := I) (M := M) g gm 2)
        (pureTrace (I := I) (M := M) g gm 4) := by
  rfl

namespace RicciDeTurckLowOrder

def monoPerm (σ : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 6) :=
  ((finSumFinEquiv (m := 4) (n := 2)).permCongr
    (Equiv.sumCongr σ (Equiv.refl (Fin 2)))).trans deTurckLieCovariantDerivativePairTracePermutation

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem curvMono_eq
    (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (σ : Equiv.Perm (Fin 4)) :
    curvatureDecompositionMonomialCoeffField (I := I) (M := M) g gm
        (ccTensorUnitValueSection (I := I) (M := M) g S)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g S) σ =
      ccOperatorFieldComp (I := I) (M := M) g 4 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm)
        (rsDomDomCongrSection (I := I) (M := M) g 4 6
          (monoPerm σ)
          (slotExtendIter (I := I) (M := M) g 0 2 4 S)) := by
  have hperm : monoPerm σ = lowMonoPerm σ := by
    rfl
  rw [hperm]
  exact curvMono_pair (I := I) (M := M) g gm S σ

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem pairTrace_eq
    (g gm : SmoothRiemannianMetric I M) :
    cometricDoublePairTraceCoefficient (I := I) (M := M) g gm =
      ccOperatorFieldComp (I := I) (M := M) g 6 4 2
        (pureTrace (I := I) (M := M) g gm 2)
        (pureTrace (I := I) (M := M) g gm 4) := by
  exact lcvPair_eq (I := I) (M := M) g gm

end RicciDeTurckLowOrder

private theorem lcvArm2_h2_rf
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) := by
  obtain ⟨Kc, hKc, hconn⟩ :=
    conn_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := fr ^ 2 * Kc
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K := mul_nonneg (pow_nonneg hfr 2) hKc
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hper : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 3 4 q
          (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g₁)‖ ^ 2 ≤
        fr ^ 2 *
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connectionDifferenceSection (I := I) g₁ g)‖ ^ 2 := by
    intro q
    let F : M → ℝ := fun x => fr ^ 2 *
      riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
        ((iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) g₁ g)).toSection x)
    have hF : MeasureTheory.Integrable F
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      dsimp only [F]
      exact (integrable_riemannianFiberNormSq_toSection
        (I := I) (M := M) g 1 (2 + q)
        (iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) g₁ g))).const_mul _
    have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g 3 (4 + q)
      (iteratedCovGrad (I := I) g 3 4 q
        (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g₁))
      F hF (fun x => by
        simpa only [F, fr] using
          deTurckLieCovariantDerivativeArmTwoCoefficient_l2 (I := I) (M := M) g g₁ q x)
    have hint : (∫ x,
        riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
          ((iteratedCovGrad (I := I) g 1 2 q
            (connectionDifferenceSection (I := I) g₁ g)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connectionDifferenceSection (I := I) g₁ g)‖ ^ 2 := by
      rw [SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
    dsimp only [F] at hsq
    rw [MeasureTheory.integral_const_mul, hint] at hsq
    exact hsq
  unfold covariantJetNormSq
  calc
    ∑ q ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 3 4 q
          (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g₁)‖ ^ 2 ≤
      ∑ q ∈ Finset.range 3, fr ^ 2 *
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) g₁ g)‖ ^ 2 :=
      Finset.sum_le_sum fun q _ => hper q
    _ = fr ^ 2 * ∑ q ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) g₁ g)‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ fr ^ 2 * (Kc *
        (1 + ∑ q ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 q P‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (hconn g₁ P hP htie hδ_le hδ0 hδ)
        (pow_nonneg hfr 2)
    _ = K * (1 + ∑ q ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 0 2 q P‖ ^ 2) := by
      simp only [K]
      ring

private theorem lcvArm2_h2
    (g : SmoothRiemannianMetric I M) :
    ∀ g₁ : SmoothRiemannianMetric I M,
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g₁) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 *
          covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceSection (I := I) g₁ g) := by
  intro g₁
  let fr : ℝ := Module.finrank ℝ E
  have hper : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 3 4 q
          (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g₁)‖ ^ 2 ≤
        fr ^ 2 *
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connectionDifferenceSection (I := I) g₁ g)‖ ^ 2 := by
    intro q
    let F : M → ℝ := fun x => fr ^ 2 *
      riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
        ((iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) g₁ g)).toSection x)
    have hF : MeasureTheory.Integrable F
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      dsimp only [F]
      exact (integrable_riemannianFiberNormSq_toSection
        (I := I) (M := M) g 1 (2 + q)
        (iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) g₁ g))).const_mul _
    have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g 3 (4 + q)
      (iteratedCovGrad (I := I) g 3 4 q
        (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g₁))
      F hF (fun x => by
        simpa only [F, fr] using
          deTurckLieCovariantDerivativeArmTwoCoefficient_l2 (I := I) (M := M) g g₁ q x)
    have hint : (∫ x,
        riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
          ((iteratedCovGrad (I := I) g 1 2 q
            (connectionDifferenceSection (I := I) g₁ g)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connectionDifferenceSection (I := I) g₁ g)‖ ^ 2 := by
      rw [SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
    dsimp only [F] at hsq
    rw [MeasureTheory.integral_const_mul, hint] at hsq
    exact hsq
  unfold covariantJetNormSq
  calc
    ∑ q ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 3 4 q
          (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g₁)‖ ^ 2 ≤
      ∑ q ∈ Finset.range 3, fr ^ 2 *
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) g₁ g)‖ ^ 2 :=
      Finset.sum_le_sum fun q _ => hper q
    _ = fr ^ 2 * ∑ q ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) g₁ g)‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem lcvArm2_h2_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g₁) ≤
        (D R * A) ^ 2 := by
  obtain ⟨Bc, hBc, hconn⟩ :=
    conn_h2_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  let fr : ℝ := Module.finrank ℝ E
  let D : ℝ → ℝ := fun R => fr * Bc R
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨D, fun R hR => mul_nonneg hfr (hBc R hR), ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ R A hR hA hP2 hP3
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g₁) ≤
      fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceSection (I := I) g₁ g) := by
          simpa only [fr] using
            lcvArm2_h2 (I := I) (M := M) g g₁
    _ ≤ fr ^ 2 * (Bc R * A) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (hconn g₁ P hP htie hδ_le hδ0 hδ
          R A hR hA hP2 hP3)
        (sq_nonneg fr)
    _ = (D R * A) ^ 2 := by
      simp only [D]
      ring

private theorem lcvPair_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 2 := by
  obtain ⟨K₂, hK₂, htrace₂⟩ :=
    trace_h2_rf (I := I) (M := M) 2 g hδ₀0 hδ₀
  obtain ⟨K₄, hK₄, htrace₄⟩ :=
    trace_h2_rf (I := I) (M := M) 4 g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 6 4 2
  let K : ℝ := Ca * K₂ * K₄
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hCa hK₂) hK₄
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hP₂ : H2Poly (I := I) (M := M) g P 1 K₂
      (pureTrace (I := I) (M := M) g g₁ 2) := by
    refine ⟨hK₂, ?_⟩
    have h :=
      htrace₂ g₁ P hP htie hδ_le hδ0 hδ (Equiv.refl (Fin 4))
    rw [reindexedPureTrace, reindex_h2] at h
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g g₁ 2) ≤
        K₂ * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := h
      _ ≤ K₂ * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl
            (covariantJetNormSq_mono (I := I) (M := M) g (by omega) P)) hK₂
      _ = K₂ * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 1 := by
        rw [pow_one]
  have hP₄ : H2Poly (I := I) (M := M) g P 1 K₄
      (pureTrace (I := I) (M := M) g g₁ 4) := by
    refine ⟨hK₄, ?_⟩
    have h :=
      htrace₄ g₁ P hP htie hδ_le hδ0 hδ (Equiv.refl (Fin 6))
    rw [reindexedPureTrace, reindex_h2] at h
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g g₁ 4) ≤
        K₄ * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := h
      _ ≤ K₄ * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl
            (covariantJetNormSq_mono (I := I) (M := M) g (by omega) P)) hK₄
      _ = K₄ * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 1 := by
        rw [pow_one]
  have hPair :=
    hp_app_of (I := I) (M := M) g P Ca hCa
      (happ (pureTrace (I := I) (M := M) g g₁ 2)
        (pureTrace (I := I) (M := M) g g₁ 4))
      hP₂ hP₄
  rw [lcvPair_eq (I := I) (M := M) g g₁]
  simpa only [K, Nat.reduceAdd] using hPair.2

private theorem lcvPair_h2_low
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R : ℝ), 0 ≤ R →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g g₁) ≤ B R := by
  obtain ⟨K2, hK2, htrace2⟩ :=
    trace_h2_rf (I := I) (M := M) 2 g hδ₀0 hδ₀
  obtain ⟨K4, hK4, htrace4⟩ :=
    trace_h2_rf (I := I) (M := M) 4 g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 6 4 2
  let B : ℝ → ℝ := fun R =>
    Ca * (K2 * (1 + R ^ 2)) * (K4 * (1 + R ^ 2))
  refine ⟨B, fun R hR =>
    mul_nonneg
      (mul_nonneg hCa (mul_nonneg hK2 (by positivity)))
      (mul_nonneg hK4 (by positivity)), ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ R hR hP2
  have hP2tr :
      covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g g₁ 2) ≤
        K2 * (1 + R ^ 2) := by
    have h := htrace2 g₁ P hP htie hδ_le hδ0 hδ
      (Equiv.refl (Fin 4))
    rw [reindexedPureTrace, reindex_h2] at h
    exact h.trans
      (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl hP2) hK2)
  have hP4tr :
      covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g g₁ 4) ≤
        K4 * (1 + R ^ 2) := by
    have h := htrace4 g₁ P hP htie hδ_le hδ0 hδ
      (Equiv.refl (Fin 6))
    rw [reindexedPureTrace, reindex_h2] at h
    exact h.trans
      (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl hP2) hK4)
  rw [lcvPair_eq (I := I) (M := M) g g₁]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g 6 4 2
          (pureTrace (I := I) (M := M) g g₁ 2)
          (pureTrace (I := I) (M := M) g g₁ 4)) ≤
      Ca * covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g g₁ 2) *
        covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g g₁ 4) :=
      happ _ _
    _ ≤ Ca * (K2 * (1 + R ^ 2)) *
        (K4 * (1 + R ^ 2)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hP2tr hCa) hP4tr
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
          (pureTrace (I := I) (M := M) g g₁ 4))
        (mul_nonneg hCa (mul_nonneg hK2 (by positivity)))
    _ = B R := by rfl

theorem exists_ricciConnectionDerivativeTransposedCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ, (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g g₁ W) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨Kf, hKf, hfull⟩ :=
    full_slot_h2_low (I := I) (M := M) g 1
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Cw, hCw, happW⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 2 2
  obtain ⟨Cm, hCm, hmono⟩ :=
    curvMono_h2 (I := I) (M := M) hDim g
  let Kpair : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (cometricDoublePairTraceCoefficient (I := I) (M := M) g g)
  obtain ⟨Kd, hKd, hdag⟩ :=
    exists_ricciConnectionDerivativeCoefficient_covariantJetNormSq_two_radiusFree_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Co, hCo, happO⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 3 4 2
  let Zw : ℝ → ℝ := fun R => Cw * (Kf * (1 + R ^ 2)) * R ^ 2
  let Zt : ℝ → ℝ := fun R => 4 * Cm * Kpair * Zw R
  let L : ℝ → ℝ := fun R => Co * Zt R * Kd
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hZw : ∀ R : ℝ, 0 ≤ R → 0 ≤ Zw R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg hCw (mul_nonneg hKf (add_nonneg (by norm_num) (sq_nonneg R))))
      (sq_nonneg R)
  have hKpair : 0 ≤ Kpair :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hZt : ∀ R : ℝ, 0 ≤ R → 0 ≤ Zt R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hCm) hKpair)
      (hZw R hR)
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCo (hZt R hR)) hKd
  refine ⟨B, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P W hP htie δ hδ_le hδ0 hδ R A hR hA hP2 hP3 hW2
  have hFull : covariantJetNormSq (I := I) (M := M) g 2
      (slotInsertEndoCc (I := I) (M := M) g 1
        (metricComparisonEndomorphismField (I := I) (M := M) g g₁)) ≤
      Kf * (1 + R ^ 2) := by
    refine (hfull g₁ P hP htie hδ_le hδ0 hδ).trans ?_
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hP2) hKf
  have hWeight : covariantJetNormSq (I := I) (M := M) g 2
      (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g g₁ W) ≤ Zw R := by
    rw [RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight]
    refine (happW _ _).trans ?_
    calc
      Cw * covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 1
            (metricComparisonEndomorphismField (I := I) (M := M) g g₁)) *
          covariantJetNormSq (I := I) (M := M) g 2 W ≤
        Cw * (Kf * (1 + R ^ 2)) * R ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hFull hCw) hW2
            (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g W)
            (mul_nonneg hCw (mul_nonneg hKf
              (add_nonneg (by norm_num) (sq_nonneg R))))
      _ = Zw R := rfl
  have hMono (σ : Equiv.Perm (Fin 4)) :
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M) g g₁ W σ) ≤
        Cm * Kpair * Zw R := by
    rw [RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial]
    calc
      _ ≤ Cm * covariantJetNormSq (I := I) (M := M) g 2
            (cometricDoublePairTraceCoefficient (I := I) (M := M) g g) *
          covariantJetNormSq (I := I) (M := M) g 2
            (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g g₁ W) := by
              exact hmono g
                (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g g₁ W) σ
      _ ≤ Cm * Kpair * Zw R :=
        mul_le_mul le_rfl hWeight
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCm hKpair)
  have hTrans : covariantJetNormSq (I := I) (M := M) g 2
      (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g g₁ W) ≤ Zt R := by
    rw [RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient]
    refine (covariantJetNormSq_sub_le (I := I) (M := M) g 2 _ _).trans ?_
    calc
      2 * (covariantJetNormSq (I := I) (M := M) g 2
            (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M)
              g g₁ W RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation) +
          covariantJetNormSq (I := I) (M := M) g 2
            (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M)
              g g₁ W RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap)) ≤
        2 * (Cm * Kpair * Zw R + Cm * Kpair * Zw R) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (hMono RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation)
              (hMono RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap)) (by norm_num)
      _ = Zt R := by simp only [Zt]; ring
  have hDag : covariantJetNormSq (I := I) (M := M) g 2
      (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g g₁) ≤
      Kd * (1 + A ^ 2) := by
    refine (hdag g₁ P hP htie hδ_le hδ0 hδ).trans ?_
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hP3) hKd
  rw [RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient]
  refine (happO _ _).trans ?_
  calc
    Co * covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g g₁ W) *
        covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g g₁) ≤
      Co * Zt R * (Kd * (1 + A ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hTrans hCo) hDag
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCo (hZt R hR))
    _ = L R * (1 + A ^ 2) := by simp only [L]; ring
    _ ≤ L R * (1 + A) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (hL R hR)
      nlinarith only [hA]
    _ = (B R * (1 + A)) ^ 2 := by
      rw [mul_pow, show B R ^ 2 = L R by
        simpa only [B] using Real.sq_sqrt (hL R hR)]

private theorem lieSecondOrderExpansion_sobolev_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ_le : δ ≤ (1 : ℝ) / 3) (_hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R : ℝ) (_hR0 : 0 ≤ R) (_hR1 : R ≤ 1)
        (_hT2 : covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2)
        {s : ℝ} (_hs : s ∈ Set.Icc (0 : ℝ) 1),
      covariantJetNormSq (I := I) (M := M) g 2
          (lieDecomposition2 (I := I) (M := M) g T hδ hδZ s) ≤
        (C * R) ^ 2 := by
  obtain ⟨Cm, hCm, hmono⟩ :=
    curvMono_h2 (I := I) (M := M) hDim g
  obtain ⟨Bp, hBp, hpair⟩ :=
    lcvPair_h2_low (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let Z : ℝ := 10 * Cm * Bp 1
  let C : ℝ := Real.sqrt Z
  have hZ : 0 ≤ Z :=
    mul_nonneg (mul_nonneg (by norm_num) hCm)
      (hBp 1 (by norm_num))
  refine ⟨C, Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ R hR0 hR1 hT2 s hs
  let P : SmoothCcTensor g 0 2 :=
    convexPerturbation (I := I) g T 0 s
  let gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδ hδZ s
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v :=
    fun x u v => metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hδ hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    convert convexPerturbation_gFibreOpBound
      (I := I) (M := M) g T 0 hδ hδZ hs.1 hs.2 using 1
    all_goals ring
  have hcP : P = s • T := by
    simp only [P, convexPerturbation, smul_zero, zero_add]
  have hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    rw [hcP]
    simp only [ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith only [hs.1, hs.2]
  have hR2one : R ^ 2 ≤ (1 : ℝ) := by
    nlinarith only [hR0, hR1]
  have hP2one :
      covariantJetNormSq (I := I) (M := M) g 2 P ≤ (1 : ℝ) ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    calc
      s ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 T ≤
          covariantJetNormSq (I := I) (M := M) g 2 T :=
        mul_le_of_le_one_left
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T) hs2
      _ ≤ R ^ 2 := hT2
      _ ≤ (1 : ℝ) ^ 2 := by norm_num at hR2one ⊢; exact hR2one
  have hPair :
      covariantJetNormSq (I := I) (M := M) g 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm) ≤ Bp 1 :=
    hpair gm P hP htie hδ_le hδ0 hδP
      1 (by norm_num) hP2one
  have hsymm : symmS (I := I) (M := M) g T = T :=
    symm_eq_self (I := I) (M := M) g T hT
  let V : Fin 3 → SmoothCcTensor g 4 2 := fun i =>
    curvatureDecompositionMonomialCoeffField (I := I) (M := M) g gm
      (ccTensorUnitValueSection (I := I) (M := M) g
        (symmS (I := I) (M := M) g T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g
        (symmS (I := I) (M := M) g T)) (lieDecompositionQ i)
  let U : Fin 3 → SmoothCcTensor g 4 2 := fun i =>
    lieDecompositionEps i • V i
  have hV (i : Fin 3) :
      covariantJetNormSq (I := I) (M := M) g 2 (V i) ≤
        Cm * Bp 1 * R ^ 2 := by
    dsimp only [V]
    rw [hsymm]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (curvatureDecompositionMonomialCoeffField
            (I := I) (M := M) g gm
            (ccTensorUnitValueSection (I := I) (M := M) g T)
            (ccTensorUnitValueSection_contMDiff
              (I := I) (M := M) g T) (lieDecompositionQ i)) ≤
        Cm * covariantJetNormSq (I := I) (M := M) g 2
            (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm) *
          covariantJetNormSq (I := I) (M := M) g 2 T :=
        hmono gm T (lieDecompositionQ i)
      _ ≤ Cm * Bp 1 *
          covariantJetNormSq (I := I) (M := M) g 2 T :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPair hCm)
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T)
      _ ≤ Cm * Bp 1 * R ^ 2 :=
        mul_le_mul_of_nonneg_left hT2
          (mul_nonneg hCm (hBp 1 (by norm_num)))
  have hU (i : Fin 3) :
      covariantJetNormSq (I := I) (M := M) g 2 (U i) ≤
        Cm * Bp 1 * R ^ 2 := by
    dsimp only [U]
    rw [covariantJetNormSq_smul]
    have heps : lieDecompositionEps i ^ 2 = (1 : ℝ) := by
      fin_cases i <;> norm_num [lieDecompositionEps]
    rw [heps, one_mul]
    exact hV i
  have hdecomposition :
      lieDecomposition2 (I := I) (M := M) g T hδ hδZ s =
        s • (U 0 + U 1 + U 2) := by
    rw [lieDecomposition2,
      deTurckLieCovariantDerivativeDecompositionC2Family_eq_symmS_weight]
    simp only [Fin.sum_univ_three, U, V, gm]
  have h01 :
      covariantJetNormSq (I := I) (M := M) g 2 (U 0 + U 1) ≤
        4 * (Cm * Bp 1 * R ^ 2) := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (U 0 + U 1) ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 2 (U 0) +
            covariantJetNormSq (I := I) (M := M) g 2 (U 1)) :=
        covariantJetNormSq_add_le (I := I) (M := M) g 2 (U 0) (U 1)
      _ ≤ 4 * (Cm * Bp 1 * R ^ 2) := by
        nlinarith only [hU 0, hU 1]
  have hsum :
      covariantJetNormSq (I := I) (M := M) g 2 (U 0 + U 1 + U 2) ≤
        10 * (Cm * Bp 1 * R ^ 2) := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (U 0 + U 1 + U 2) ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 2 (U 0 + U 1) +
            covariantJetNormSq (I := I) (M := M) g 2 (U 2)) :=
        covariantJetNormSq_add_le (I := I) (M := M) g 2 (U 0 + U 1) (U 2)
      _ ≤ 10 * (Cm * Bp 1 * R ^ 2) := by
        nlinarith only [h01, hU 2]
  rw [hdecomposition, covariantJetNormSq_smul]
  calc
    s ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 (U 0 + U 1 + U 2) ≤
        covariantJetNormSq (I := I) (M := M) g 2 (U 0 + U 1 + U 2) :=
      mul_le_of_le_one_left
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
          (U 0 + U 1 + U 2)) hs2
    _ ≤ 10 * (Cm * Bp 1 * R ^ 2) := hsum
    _ = (C * R) ^ 2 := by
      have hsqrt : Real.sqrt Z ^ 2 = Z := Real.sq_sqrt hZ
      simp only [C, Z, mul_pow, hsqrt]
      ring

private theorem ricciTop_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P T : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ (1 : ℝ) / 3) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R : ℝ) (_hR0 : 0 ≤ R)
        (_hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ 1)
        (_hT2 : covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2),
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T) ≤
        (C * R) ^ 2 := by
  obtain ⟨Kf, hKf, hfull⟩ :=
    full_slot_h2_low (I := I) (M := M) g 1
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Cw, hCw, happW⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 2 2
  obtain ⟨Cm, hCm, hmono⟩ :=
    curvMono_h2 (I := I) (M := M) hDim g
  let Kpair : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (cometricDoublePairTraceCoefficient (I := I) (M := M) g g)
  obtain ⟨Kc, hKc, hconn⟩ :=
    connLow_h2_low (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Cd, hCd, happD⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 4 4 4
  let Kperm : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciConnectionDifferenceDerivativeCyclicPermutation)
  let fr : ℝ := Module.finrank ℝ E
  obtain ⟨Co, hCo, happO⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 4 4 2
  let Kw : ℝ := Cw * (2 * Kf)
  let Km : ℝ := Cm * Kpair * Kw
  let Kt : ℝ := 4 * Km
  let Kd : ℝ := Cd * Kperm * (fr * (2 * Kc))
  let Z : ℝ := Co * Kt * Kd
  let C : ℝ := Real.sqrt Z
  have hKpair : 0 ≤ Kpair :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hKperm : 0 ≤ Kperm :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hKw : 0 ≤ Kw :=
    mul_nonneg hCw (mul_nonneg (by norm_num) hKf)
  have hKm : 0 ≤ Km := mul_nonneg (mul_nonneg hCm hKpair) hKw
  have hKt : 0 ≤ Kt := mul_nonneg (by norm_num) hKm
  have hKd : 0 ≤ Kd :=
    mul_nonneg (mul_nonneg hCd hKperm)
      (mul_nonneg hfr (mul_nonneg (by norm_num) hKc))
  have hZ : 0 ≤ Z := mul_nonneg (mul_nonneg hCo hKt) hKd
  refine ⟨C, Real.sqrt_nonneg _, ?_⟩
  intro gm P T hP htie δ hδ_le hδ0 hδ R hR0 hP2 hT2
  have hFull :
      covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 1
            (metricComparisonEndomorphismField (I := I) (M := M) g gm)) ≤
        2 * Kf := by
    calc
      _ ≤ Kf * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) :=
        hfull gm P hP htie hδ_le hδ0 hδ
      _ ≤ 2 * Kf := by nlinarith only [hP2, hKf]
  have hWeight :
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm T) ≤
        Kw * R ^ 2 := by
    rw [ricciConnectionDifferenceDerivativeMetricWeight]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (slotInsertEndoCc (I := I) (M := M) g 1
              (metricComparisonEndomorphismField (I := I) (M := M) g gm)) T) ≤
        Cw * covariantJetNormSq (I := I) (M := M) g 2
            (slotInsertEndoCc (I := I) (M := M) g 1
              (metricComparisonEndomorphismField (I := I) (M := M) g gm)) *
          covariantJetNormSq (I := I) (M := M) g 2 T := by
        simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
          happW
            (slotInsertEndoCc (I := I) (M := M) g 1
              (metricComparisonEndomorphismField (I := I) (M := M) g gm)) T
      _ ≤ Cw * (2 * Kf) * R ^ 2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hFull hCw) hT2
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T)
          (mul_nonneg hCw (mul_nonneg (by norm_num) hKf))
      _ = Kw * R ^ 2 := by simp only [Kw]
  have hMono (σ : Equiv.Perm (Fin 4)) :
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M) g gm T σ) ≤
        Km * R ^ 2 := by
    rw [ricciConnectionDifferenceDerivativeTransposedMonomial]
    calc
      _ ≤ Cm * covariantJetNormSq (I := I) (M := M) g 2
            (cometricDoublePairTraceCoefficient (I := I) (M := M) g g) *
          covariantJetNormSq (I := I) (M := M) g 2
            (ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm T) :=
        hmono g (ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm T) σ
      _ ≤ Cm * Kpair * (Kw * R ^ 2) := by
        simpa only [Kpair] using
          mul_le_mul_of_nonneg_left hWeight
            (mul_nonneg hCm hKpair)
      _ = Km * R ^ 2 := by simp only [Km]; ring
  have hTrans :
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm T) ≤
        Kt * R ^ 2 := by
    rw [ricciConnectionDifferenceDerivativeTransposedCoefficient]
    calc
      _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 2
            (ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M) g gm T ricciConnectionDifferenceDerivativeCyclicPermutation) +
          covariantJetNormSq (I := I) (M := M) g 2
            (ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M) g gm T ricciConnectionDifferenceDerivativeFirstPairSwap)) :=
        covariantJetNormSq_sub_le (I := I) (M := M) g 2 _ _
      _ ≤ 4 * (Km * R ^ 2) := by
        nlinarith only [hMono ricciConnectionDifferenceDerivativeCyclicPermutation, hMono ricciConnectionDifferenceDerivativeFirstPairSwap]
      _ = Kt * R ^ 2 := by simp only [Kt]; ring
  have hConn :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceLowOrderOperator (I := I) (M := M) g gm) ≤ 2 * Kc := by
    calc
      _ ≤ Kc * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) :=
        hconn gm P hP htie hδ_le hδ0 hδ
      _ ≤ 2 * Kc := by nlinarith only [hP2, hKc]
  have hSlot :
      covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 3 3
            (connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)) ≤
        fr * (2 * Kc) := by
    calc
      _ ≤ (Module.finrank ℝ E : ℝ) *
          covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceLowOrderOperator (I := I) (M := M) g gm) :=
        slot_h2 (I := I) (M := M) g 3 3 _
      _ ≤ fr * (2 * Kc) :=
        mul_le_mul_of_nonneg_left hConn hfr
  have hDag :
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm) ≤ Kd := by
    rw [ricciConnectionPrincipalCoefficient]
    calc
      _ ≤ Cd * covariantJetNormSq (I := I) (M := M) g 2
            (permCoeff (I := I) (M := M) g ricciConnectionDifferenceDerivativeCyclicPermutation) *
          covariantJetNormSq (I := I) (M := M) g 2
            (slotExtend (I := I) (M := M) g 3 3
              (connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)) :=
        happD _ _
      _ ≤ Cd * Kperm * (fr * (2 * Kc)) := by
        simpa only [Kperm] using
          mul_le_mul_of_nonneg_left hSlot
            (mul_nonneg hCd hKperm)
      _ = Kd := by rfl
  rw [ricciConnectionDifferenceTopOrderCoefficient, ricciCovariantDerivativeConnectionDifferenceTopOrder]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g 4 4 2
          (ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm T)
          (ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm)) ≤
      Co * covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm T) *
        covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm) :=
      happO _ _
    _ ≤ Co * (Kt * R ^ 2) * Kd := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hTrans hCo) hDag
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
          (ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm))
        (mul_nonneg hCo (mul_nonneg hKt (sq_nonneg R)))
    _ = Z * R ^ 2 := by simp only [Z]; ring
    _ = (C * R) ^ 2 := by
      rw [mul_pow, show C ^ 2 = Z by
        simpa only [C] using Real.sq_sqrt hZ]

private theorem lcvCurv_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ T : SmoothCcTensor g 0 2,
        covariantJetNormSq (I := I) (M := M) g 2
            (lcvCurv (I := I) (M := M) g T) ≤
          K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) := by
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 2 4
  let K₁ : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2
      (lcvRiem1 (I := I) (M := M) g)
  let K₂ : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2
      (lcvRiem2 (I := I) (M := M) g)
  let K : ℝ := 2 * (Ca * K₁ * 1 + Ca * K₂ * 1)
  have hK₁ : 0 ≤ K₁ :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hK₂ : 0 ≤ K₂ :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hK : 0 ≤ K :=
    mul_nonneg (by norm_num)
      (add_nonneg
        (mul_nonneg (mul_nonneg hCa hK₁) (by norm_num))
        (mul_nonneg (mul_nonneg hCa hK₂) (by norm_num)))
  refine ⟨K, hK, ?_⟩
  intro T
  have hT : H2Poly (I := I) (M := M) g T 1 1 T := by
    refine ⟨by norm_num, ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2 T ≤
        covariantJetNormSq (I := I) (M := M) g 3 T :=
          covariantJetNormSq_mono (I := I) (M := M) g (by omega) T
      _ ≤ 1 * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 1 := by
        simp only [one_mul, pow_one]
        linarith
  have hR₁ :
      H2Poly (I := I) (M := M) g T 0 K₁
        (lcvRiem1 (I := I) (M := M) g) := by
    simpa only [K₁] using
      hp_const (I := I) (M := M) g T
        (lcvRiem1 (I := I) (M := M) g)
  have hR₂ :
      H2Poly (I := I) (M := M) g T 0 K₂
        (lcvRiem2 (I := I) (M := M) g) := by
    simpa only [K₂] using
      hp_const (I := I) (M := M) g T
        (lcvRiem2 (I := I) (M := M) g)
  have hA :=
    hp_app_of (I := I) (M := M) g T Ca hCa
      (happ (lcvRiem1 (I := I) (M := M) g) T)
      hR₁ hT
  have hB :=
    hp_app_of (I := I) (M := M) g T Ca hCa
      (happ (lcvRiem2 (I := I) (M := M) g) T)
      hR₂ hT
  have hSum := hp_add (I := I) (M := M) g T hA hB
  simpa only [lcvCurv, K, Nat.zero_add, mul_one, pow_one] using hSum.2

private theorem lcvCurv_h2_lin
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ T : SmoothCcTensor g 0 2,
        covariantJetNormSq (I := I) (M := M) g 2
            (lcvCurv (I := I) (M := M) g T) ≤
          K * covariantJetNormSq (I := I) (M := M) g 2 T := by
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 2 4
  let K1 : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2
      (lcvRiem1 (I := I) (M := M) g)
  let K2 : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2
      (lcvRiem2 (I := I) (M := M) g)
  let K : ℝ := 2 * Ca * (K1 + K2)
  have hK1 : 0 ≤ K1 :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hK2 : 0 ≤ K2 :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hK : 0 ≤ K :=
    mul_nonneg (mul_nonneg (by norm_num) hCa)
      (add_nonneg hK1 hK2)
  refine ⟨K, hK, ?_⟩
  intro T
  let Y1 : SmoothCcTensor g 0 4 :=
    operatorFieldApply (I := I) (M := M) g 2 4
      (lcvRiem1 (I := I) (M := M) g) T
  let Y2 : SmoothCcTensor g 0 4 :=
    operatorFieldApply (I := I) (M := M) g 2 4
      (lcvRiem2 (I := I) (M := M) g) T
  have hY1 :
      covariantJetNormSq (I := I) (M := M) g 2 Y1 ≤
        Ca * K1 * covariantJetNormSq (I := I) (M := M) g 2 T := by
    simpa only [Y1, K1, operatorFieldComposition_zero_eq_operatorFieldApply] using
      happ (lcvRiem1 (I := I) (M := M) g) T
  have hY2 :
      covariantJetNormSq (I := I) (M := M) g 2 Y2 ≤
        Ca * K2 * covariantJetNormSq (I := I) (M := M) g 2 T := by
    simpa only [Y2, K2, operatorFieldComposition_zero_eq_operatorFieldApply] using
      happ (lcvRiem2 (I := I) (M := M) g) T
  change covariantJetNormSq (I := I) (M := M) g 2 (Y1 + Y2) ≤ _
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (Y1 + Y2) ≤
      2 * (covariantJetNormSq (I := I) (M := M) g 2 Y1 +
        covariantJetNormSq (I := I) (M := M) g 2 Y2) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 2 Y1 Y2
    _ ≤ 2 * (Ca * K1 * covariantJetNormSq (I := I) (M := M) g 2 T +
        Ca * K2 * covariantJetNormSq (I := I) (M := M) g 2 T) :=
      mul_le_mul_of_nonneg_left (add_le_add hY1 hY2) (by norm_num)
    _ = K * covariantJetNormSq (I := I) (M := M) g 2 T := by
      simp only [K]
      ring

omit [NeZero (Module.finrank ℝ E)] in
private theorem raise0_l2_sq
    (g : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (q : ℕ) :
    ‖iteratedCovGrad (I := I) g 1 1 q
        (cometricRaiseSlot0Field (I := I) (M := M) g 0 W)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g 0 2 q W‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq
    (I := I) (M := M) g 0 W q x

omit [NeZero (Module.finrank ℝ E)] in
private theorem raise0_jet
    (g : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (m : ℕ) :
    covariantJetNormSq (I := I) (M := M) g m
        (cometricRaiseSlot0Field (I := I) (M := M) g 0 W) =
      covariantJetNormSq (I := I) (M := M) g m W := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro q _
  exact raise0_l2_sq (I := I) (M := M) g W q

private theorem fullRev_slot_h3
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v),
      covariantJetNormSq (I := I) (M := M) g 3
          (slotInsertEndoCc (I := I) (M := M) g s
            (metricComparisonEndomorphismField (I := I) (M := M) g₁ g)) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) := by
  let fr : ℝ := Module.finrank ℝ E
  let B : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 3
      (slotInsertEndoCc (I := I) (M := M) g 0
        (metricComparisonEndomorphismField (I := I) (M := M) g g))
  let K : ℝ := fr ^ s * (2 * (B + 1))
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hB : 0 ≤ B :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g _
  have hK : 0 ≤ K :=
    mul_nonneg (pow_nonneg hfr s)
      (mul_nonneg (by norm_num) (add_nonneg hB (by norm_num)))
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symm_eq_self (I := I) (M := M) g P hP
  have hrev0 :
      covariantJetNormSq (I := I) (M := M) g 3
          (slotInsertEndoCc (I := I) (M := M) g 0
            (metricComparisonEndomorphismField (I := I) (M := M) g₁ g)) ≤
        2 * (B + covariantJetNormSq (I := I) (M := M) g 3 P) := by
    calc
      covariantJetNormSq (I := I) (M := M) g 3
          (slotInsertEndoCc (I := I) (M := M) g 0
            (metricComparisonEndomorphismField (I := I) (M := M) g₁ g)) =
        covariantJetNormSq (I := I) (M := M) g 3
          (omRecoverEndoCc (I := I) g g₁) := by
            rw [fullRev0_eq (I := I) (M := M) g g₁]
      _ = covariantJetNormSq (I := I) (M := M) g 3
          (slotInsertEndoCc (I := I) (M := M) g 0
              (metricComparisonEndomorphismField (I := I) (M := M) g g) +
            cometricRaiseSlot0Field (I := I) (M := M) g 0
              (symmS (I := I) (M := M) g P)) := by
            rw [omRecover_add (I := I) (M := M) g g₁ P htie]
      _ ≤ 2 * (
          covariantJetNormSq (I := I) (M := M) g 3
            (slotInsertEndoCc (I := I) (M := M) g 0
              (metricComparisonEndomorphismField (I := I) (M := M) g g)) +
          covariantJetNormSq (I := I) (M := M) g 3
            (cometricRaiseSlot0Field (I := I) (M := M) g 0
              (symmS (I := I) (M := M) g P))) :=
        covariantJetNormSq_add_le (I := I) (M := M) g 3 _ _
      _ = 2 * (B + covariantJetNormSq (I := I) (M := M) g 3 P) := by
        rw [hsymm, raise0_jet (I := I) (M := M) g P 3]
  have hP3 :
      0 ≤ covariantJetNormSq (I := I) (M := M) g 3 P :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g P
  have hbase :
      B + covariantJetNormSq (I := I) (M := M) g 3 P ≤
        (B + 1) *
          (1 + covariantJetNormSq (I := I) (M := M) g 3 P) := by
    nlinarith only [mul_nonneg hB hP3]
  calc
    covariantJetNormSq (I := I) (M := M) g 3
        (slotInsertEndoCc (I := I) (M := M) g s
          (metricComparisonEndomorphismField (I := I) (M := M) g₁ g)) ≤
      fr ^ s * covariantJetNormSq (I := I) (M := M) g 3
        (slotInsertEndoCc (I := I) (M := M) g 0
          (metricComparisonEndomorphismField (I := I) (M := M) g₁ g)) := by
      simpa only [fr] using
        endo_slot_h3 (I := I) (M := M) g s
          (metricComparisonEndomorphismField (I := I) (M := M) g₁ g)
    _ ≤ fr ^ s *
        (2 * (B + covariantJetNormSq (I := I) (M := M) g 3 P)) :=
      mul_le_mul_of_nonneg_left hrev0 (pow_nonneg hfr s)
    _ ≤ fr ^ s *
        (2 * ((B + 1) *
          (1 + covariantJetNormSq (I := I) (M := M) g 3 P))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbase (by norm_num))
        (pow_nonneg hfr s)
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) := by
      simp only [K]
      ring

private theorem fullRev_slot_h2_low
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v),
      covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g s
            (metricComparisonEndomorphismField (I := I) (M := M) g₁ g)) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  let fr : ℝ := Module.finrank ℝ E
  let B : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2
      (slotInsertEndoCc (I := I) (M := M) g 0
        (metricComparisonEndomorphismField (I := I) (M := M) g g))
  let K : ℝ := fr ^ s * (2 * (B + 1))
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hB : 0 ≤ B :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hK : 0 ≤ K :=
    mul_nonneg (pow_nonneg hfr s)
      (mul_nonneg (by norm_num) (add_nonneg hB (by norm_num)))
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symm_eq_self (I := I) (M := M) g P hP
  have hrev0 :
      covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 0
            (metricComparisonEndomorphismField (I := I) (M := M) g₁ g)) ≤
        2 * (B + covariantJetNormSq (I := I) (M := M) g 2 P) := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 0
            (metricComparisonEndomorphismField (I := I) (M := M) g₁ g)) =
        covariantJetNormSq (I := I) (M := M) g 2
          (omRecoverEndoCc (I := I) g g₁) := by
            rw [fullRev0_eq (I := I) (M := M) g g₁]
      _ = covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 0
              (metricComparisonEndomorphismField (I := I) (M := M) g g) +
            cometricRaiseSlot0Field (I := I) (M := M) g 0
              (symmS (I := I) (M := M) g P)) := by
            rw [omRecover_add (I := I) (M := M) g g₁ P htie]
      _ ≤ 2 * (
          covariantJetNormSq (I := I) (M := M) g 2
            (slotInsertEndoCc (I := I) (M := M) g 0
              (metricComparisonEndomorphismField (I := I) (M := M) g g)) +
          covariantJetNormSq (I := I) (M := M) g 2
            (cometricRaiseSlot0Field (I := I) (M := M) g 0
              (symmS (I := I) (M := M) g P))) :=
        covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _
      _ = 2 * (B + covariantJetNormSq (I := I) (M := M) g 2 P) := by
        rw [hsymm, raise0_jet (I := I) (M := M) g P 2]
  have hP2 :
      0 ≤ covariantJetNormSq (I := I) (M := M) g 2 P :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g P
  have hbase :
      B + covariantJetNormSq (I := I) (M := M) g 2 P ≤
        (B + 1) *
          (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
    nlinarith only [mul_nonneg hB hP2]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g s
          (metricComparisonEndomorphismField (I := I) (M := M) g₁ g)) ≤
      fr ^ s * covariantJetNormSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g 0
          (metricComparisonEndomorphismField (I := I) (M := M) g₁ g)) := by
      simpa only [fr] using
        endo_slot_h2 (I := I) (M := M) g s
          (metricComparisonEndomorphismField (I := I) (M := M) g₁ g)
    _ ≤ fr ^ s *
        (2 * (B + covariantJetNormSq (I := I) (M := M) g 2 P)) :=
      mul_le_mul_of_nonneg_left hrev0 (pow_nonneg hfr s)
    _ ≤ fr ^ s *
        (2 * ((B + 1) *
          (1 + covariantJetNormSq (I := I) (M := M) g 2 P))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbase (by norm_num))
        (pow_nonneg hfr s)
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
      simp only [K]
      ring

private theorem lcvOmega_h2_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lcvOmega (I := I) (M := M) g g₁) ≤
        (D R * A) ^ 2 := by
  obtain ⟨Kr, hKr, hrev⟩ :=
    fullRev_slot_h2_low (I := I) (M := M) g 2
  obtain ⟨Bl, hBl, hlower⟩ :=
    connLower_h2_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 3 3
  let Z : ℝ → ℝ := fun R => Ca * (Kr * (1 + R ^ 2))
  let D : ℝ → ℝ := fun R => Real.sqrt (Z R) * Bl R
  have hZ : ∀ R : ℝ, 0 ≤ Z R :=
    fun R => mul_nonneg hCa
      (mul_nonneg hKr (by positivity))
  refine ⟨D, fun R hR =>
    mul_nonneg (Real.sqrt_nonneg _) (hBl R hR), ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ R A hR hA hP2 hP3
  have hR0 : H2Poly (I := I) (M := M) g P 0
      (Kr * (1 + R ^ 2))
      (slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M) g₁ g)) := by
    refine ⟨mul_nonneg hKr (by positivity), ?_⟩
    simpa only [pow_zero, mul_one] using
      (hrev g₁ P hP htie).trans
        (mul_le_mul_of_nonneg_left
          (add_le_add le_rfl hP2) hKr)
  have hL0 : H2Poly (I := I) (M := M) g P 0
      ((Bl R * A) ^ 2)
      (metricLoweredConnectionDifferenceCoefficient (I := I) g g₁) := by
    refine ⟨sq_nonneg _, ?_⟩
    simpa only [pow_zero, mul_one] using
      hlower g₁ P hP htie hδ_le hδ0 hδ
        R A hR hA hP2 hP3
  have hL :=
    hp_domperm (I := I) (M := M) g P (finRotate 3) hL0
  have hOut :=
    hp_app_of (I := I) (M := M) g P Ca hCa
      (happ
        (slotInsertEndoCc (I := I) (M := M) g 2
          (metricComparisonEndomorphismField (I := I) (M := M) g₁ g))
        (domDomCongrSection (I := I) g (finRotate 3)
          (metricLoweredConnectionDifferenceCoefficient (I := I) g g₁)))
      hR0 hL
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (lcvOmega (I := I) (M := M) g g₁) ≤
      Ca * (Kr * (1 + R ^ 2)) * (Bl R * A) ^ 2 := by
        simpa only [lcvOmega, Nat.zero_add, pow_zero, mul_one] using hOut.2
    _ = (D R * A) ^ 2 := by
      have hsqrt : (Real.sqrt (Z R)) ^ 2 = Z R :=
        Real.sq_sqrt (hZ R)
      simp only [D, mul_pow, hsqrt, Z]
      ring

private theorem lcvOmega_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (lcvOmega (I := I) (M := M) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 3 := by
  obtain ⟨Kr, hKr, hrev⟩ :=
    fullRev_slot_h3 (I := I) (M := M) g 2
  obtain ⟨Kl, hKl, hlower⟩ :=
    connLower_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 3 3
  let K : ℝ := Ca * Kr * Kl
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hCa hKr) hKl
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hR : H2Poly (I := I) (M := M) g P 1 Kr
      (slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M) g₁ g)) := by
    refine ⟨hKr, ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 2
            (metricComparisonEndomorphismField (I := I) (M := M) g₁ g)) ≤
        covariantJetNormSq (I := I) (M := M) g 3
          (slotInsertEndoCc (I := I) (M := M) g 2
            (metricComparisonEndomorphismField (I := I) (M := M) g₁ g)) :=
          covariantJetNormSq_mono (I := I) (M := M) g (by omega) _
      _ ≤ Kr * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) :=
        hrev g₁ P hP htie
      _ = Kr * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 1 := by
        rw [pow_one]
  have hL0 : H2Poly (I := I) (M := M) g P 2 Kl
      (metricLoweredConnectionDifferenceCoefficient (I := I) g g₁) := by
    refine ⟨hKl, ?_⟩
    exact hlower g₁ P hP htie hδ_le hδ0 hδ
  have hL :=
    hp_domperm (I := I) (M := M) g P (finRotate 3) hL0
  have hOut :=
    hp_app_of (I := I) (M := M) g P Ca hCa
      (happ
        (slotInsertEndoCc (I := I) (M := M) g 2
          (metricComparisonEndomorphismField (I := I) (M := M) g₁ g))
        (domDomCongrSection (I := I) g (finRotate 3)
          (metricLoweredConnectionDifferenceCoefficient (I := I) g g₁)))
      hR hL
  simpa only [lcvOmega, K, Nat.reduceAdd] using hOut.2

private theorem lcvQuad_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (lcvQuad (I := I) (M := M) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 4 := by
  obtain ⟨Kb, hKb, harm⟩ :=
    lcvArm2_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Ko, hKo, homega⟩ :=
    lcvOmega_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 3 4
  let Kq : ℝ := Ca * Kb * Ko
  let K₂ : ℝ := 2 * (Kq + Kq)
  let K₃ : ℝ := 2 * (K₂ + Kq)
  let K₄ : ℝ := 2 * (K₃ + Kq)
  let K₅ : ℝ := 2 * (K₄ + Kq)
  let K : ℝ := 2 * (K₅ + Kq)
  have hKq : 0 ≤ Kq := mul_nonneg (mul_nonneg hCa hKb) hKo
  have hK₂ : 0 ≤ K₂ :=
    mul_nonneg (by norm_num) (add_nonneg hKq hKq)
  have hK₃ : 0 ≤ K₃ :=
    mul_nonneg (by norm_num) (add_nonneg hK₂ hKq)
  have hK₄ : 0 ≤ K₄ :=
    mul_nonneg (by norm_num) (add_nonneg hK₃ hKq)
  have hK₅ : 0 ≤ K₅ :=
    mul_nonneg (by norm_num) (add_nonneg hK₄ hKq)
  have hK : 0 ≤ K :=
    mul_nonneg (by norm_num) (add_nonneg hK₅ hKq)
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hB : H2Poly (I := I) (M := M) g P 1 Kb
      (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g₁) := by
    refine ⟨hKb, ?_⟩
    simpa only [pow_one] using
      harm g₁ P hP htie hδ_le hδ0 hδ
  have hO : H2Poly (I := I) (M := M) g P 3 Ko
      (lcvOmega (I := I) (M := M) g g₁) := by
    refine ⟨hKo, ?_⟩
    exact homega g₁ P hP htie hδ_le hδ0 hδ
  have hQB : H2Poly (I := I) (M := M) g P 4 Kq
      (lcvQB (I := I) (M := M) g g₁) := by
    simpa only [lcvQB, Kq, Nat.reduceAdd] using
      hp_app_of (I := I) (M := M) g P Ca hCa
        (happ (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g₁)
          (lcvOmega (I := I) (M := M) g g₁))
        hB hO
  have hOs :=
    hp_domperm (I := I) (M := M) g P
      (Equiv.swap (0 : Fin 3) 1) hO
  have hQA : H2Poly (I := I) (M := M) g P 4 Kq
      (lcvQA (I := I) (M := M) g g₁) := by
    simpa only [lcvQA, Kq, Nat.reduceAdd] using
      hp_app_of (I := I) (M := M) g P Ca hCa
        (happ (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g₁)
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 3) 1)
            (lcvOmega (I := I) (M := M) g g₁)))
        hB hOs
  have h₁ :=
    hp_domperm (I := I) (M := M) g P
      (Equiv.swap (0 : Fin 4) 1) hQB
  have h₃ :=
    hp_domperm (I := I) (M := M) g P lcvPermA hQA
  have h₄ :=
    hp_domperm (I := I) (M := M) g P
      (Equiv.swap (0 : Fin 4) 2) hQA
  have h₅ :=
    hp_domperm (I := I) (M := M) g P lcvPermB hQA
  have h₆ :=
    hp_domperm (I := I) (M := M) g P lcvPermC hQA
  have h12 := hp_add (I := I) (M := M) g P h₁ hQB
  have h123 := hp_add (I := I) (M := M) g P h12 h₃
  have h1234 := hp_add (I := I) (M := M) g P h123 h₄
  have h12345 := hp_add (I := I) (M := M) g P h1234 h₅
  have h123456 := hp_add (I := I) (M := M) g P h12345 h₆
  simpa only [lcvQuad, Kq, K₂, K₃, K₄, K₅, K] using h123456.2

private theorem lcvQuad_h2_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lcvQuad (I := I) (M := M) g g₁) ≤
        (D R * A ^ 2) ^ 2 := by
  obtain ⟨Db, hDb, harm⟩ :=
    lcvArm2_h2_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Do, hDo, homega⟩ :=
    lcvOmega_h2_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 3 4
  let Kq : ℝ → ℝ := fun R =>
    Ca * (Db R) ^ 2 * (Do R) ^ 2
  let K₂ : ℝ → ℝ := fun R => 2 * (Kq R + Kq R)
  let K₃ : ℝ → ℝ := fun R => 2 * (K₂ R + Kq R)
  let K₄ : ℝ → ℝ := fun R => 2 * (K₃ R + Kq R)
  let K₅ : ℝ → ℝ := fun R => 2 * (K₄ R + Kq R)
  let K : ℝ → ℝ := fun R => 2 * (K₅ R + Kq R)
  let D : ℝ → ℝ := fun R => Real.sqrt (K R)
  have hKq : ∀ R : ℝ, 0 ≤ Kq R :=
    fun R => mul_nonneg
      (mul_nonneg hCa (sq_nonneg _)) (sq_nonneg _)
  have hK₂ : ∀ R : ℝ, 0 ≤ K₂ R :=
    fun R => mul_nonneg (by norm_num)
      (add_nonneg (hKq R) (hKq R))
  have hK₃ : ∀ R : ℝ, 0 ≤ K₃ R :=
    fun R => mul_nonneg (by norm_num)
      (add_nonneg (hK₂ R) (hKq R))
  have hK₄ : ∀ R : ℝ, 0 ≤ K₄ R :=
    fun R => mul_nonneg (by norm_num)
      (add_nonneg (hK₃ R) (hKq R))
  have hK₅ : ∀ R : ℝ, 0 ≤ K₅ R :=
    fun R => mul_nonneg (by norm_num)
      (add_nonneg (hK₄ R) (hKq R))
  have hK : ∀ R : ℝ, 0 ≤ K R :=
    fun R => mul_nonneg (by norm_num)
      (add_nonneg (hK₅ R) (hKq R))
  refine ⟨D, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ R A hR hA hP2 hP3
  have reweight {r s : ℕ} {S : SmoothCcTensor g r s}
      {X Y : ℝ} (hXY : X = Y)
      (hS : H2Poly (I := I) (M := M) g P 0 X S) :
      H2Poly (I := I) (M := M) g P 0 Y S := by
    rwa [← hXY]
  have hB : H2Poly (I := I) (M := M) g P 0
      ((Db R * A) ^ 2)
      (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g₁) := by
    refine ⟨sq_nonneg _, ?_⟩
    simpa only [pow_zero, mul_one] using
      harm g₁ P hP htie hδ_le hδ0 hδ
        R A hR hA hP2 hP3
  have hO : H2Poly (I := I) (M := M) g P 0
      ((Do R * A) ^ 2)
      (lcvOmega (I := I) (M := M) g g₁) := by
    refine ⟨sq_nonneg _, ?_⟩
    simpa only [pow_zero, mul_one] using
      homega g₁ P hP htie hδ_le hδ0 hδ
        R A hR hA hP2 hP3
  have hQB0 : H2Poly (I := I) (M := M) g P 0
      (Ca * (Db R * A) ^ 2 * (Do R * A) ^ 2)
      (lcvQB (I := I) (M := M) g g₁) := by
    simpa only [lcvQB, Nat.zero_add] using
      hp_app_of (I := I) (M := M) g P Ca hCa
        (happ (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g₁)
          (lcvOmega (I := I) (M := M) g g₁))
        hB hO
  have hqeq :
      Ca * (Db R * A) ^ 2 * (Do R * A) ^ 2 =
        Kq R * A ^ 4 := by
    simp only [Kq]
    ring
  have hQB := reweight hqeq hQB0
  have hOs :=
    hp_domperm (I := I) (M := M) g P
      (Equiv.swap (0 : Fin 3) 1) hO
  have hQA0 : H2Poly (I := I) (M := M) g P 0
      (Ca * (Db R * A) ^ 2 * (Do R * A) ^ 2)
      (lcvQA (I := I) (M := M) g g₁) := by
    simpa only [lcvQA, Nat.zero_add] using
      hp_app_of (I := I) (M := M) g P Ca hCa
        (happ (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g₁)
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 3) 1)
            (lcvOmega (I := I) (M := M) g g₁)))
        hB hOs
  have hQA := reweight hqeq hQA0
  have h₁ :=
    hp_domperm (I := I) (M := M) g P
      (Equiv.swap (0 : Fin 4) 1) hQB
  have h₃ :=
    hp_domperm (I := I) (M := M) g P lcvPermA hQA
  have h₄ :=
    hp_domperm (I := I) (M := M) g P
      (Equiv.swap (0 : Fin 4) 2) hQA
  have h₅ :=
    hp_domperm (I := I) (M := M) g P lcvPermB hQA
  have h₆ :=
    hp_domperm (I := I) (M := M) g P lcvPermC hQA
  have h12eq :
      2 * (Kq R * A ^ 4 + Kq R * A ^ 4) =
        K₂ R * A ^ 4 := by
    simp only [K₂]
    ring
  have h12 := reweight h12eq
    (hp_add (I := I) (M := M) g P h₁ hQB)
  have h123eq :
      2 * (K₂ R * A ^ 4 + Kq R * A ^ 4) =
        K₃ R * A ^ 4 := by
    simp only [K₃]
    ring
  have h123 := reweight h123eq
    (hp_add (I := I) (M := M) g P h12 h₃)
  have h1234eq :
      2 * (K₃ R * A ^ 4 + Kq R * A ^ 4) =
        K₄ R * A ^ 4 := by
    simp only [K₄]
    ring
  have h1234 := reweight h1234eq
    (hp_add (I := I) (M := M) g P h123 h₄)
  have h12345eq :
      2 * (K₄ R * A ^ 4 + Kq R * A ^ 4) =
        K₅ R * A ^ 4 := by
    simp only [K₅]
    ring
  have h12345 := reweight h12345eq
    (hp_add (I := I) (M := M) g P h1234 h₅)
  have h123456eq :
      2 * (K₅ R * A ^ 4 + Kq R * A ^ 4) =
        K R * A ^ 4 := by
    simp only [K]
    ring
  have h123456 := reweight h123456eq
    (hp_add (I := I) (M := M) g P h12345 h₆)
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (lcvQuad (I := I) (M := M) g g₁) ≤
      K R * A ^ 4 := by
        simpa only [lcvQuad, pow_zero, mul_one] using h123456.2
    _ = (D R * A ^ 2) ^ 2 := by
      have hsqrt : (Real.sqrt (K R)) ^ 2 = K R :=
        Real.sq_sqrt (hK R)
      simp only [D, mul_pow, hsqrt]
      ring

private theorem lcvR4_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {s : ℝ} (_hs : s ∈ Set.Icc (0 : ℝ) 1),
      covariantJetNormSq (I := I) (M := M) g 2
          (lcvR4 (I := I) (M := M) g T hδ hδZ s) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 4 := by
  obtain ⟨Kc, hKc, hcurv⟩ :=
    lcvCurv_h2 (I := I) (M := M) hDim g
  obtain ⟨Kq, hKq, hquad⟩ :=
    lcvQuad_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  let K : ℝ := 2 * (Kc + Kq)
  have hK : 0 ≤ K :=
    mul_nonneg (by norm_num) (add_nonneg hKc hKq)
  refine ⟨K, hK, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ s hs
  obtain ⟨hs0, hs1⟩ := hs
  let P : SmoothCcTensor g 0 2 := s • T
  let gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδ hδZ s
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt ⟨hs0, hs1⟩
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    rw [← show convexPerturbation (I := I) g T 0 s = P by
      simp only [P, convexPerturbation, smul_zero, zero_add]]
    exact metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hδ hδZ hs_mem x u v
  have hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [P, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδ hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs0]
      ring
    simpa only [P, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith only [hs0, hs1]
  have hPjet :
      covariantJetNormSq (I := I) (M := M) g 3 P ≤
        covariantJetNormSq (I := I) (M := M) g 3 T := by
    rw [show P = s • T by rfl, covariantJetNormSq_smul]
    exact mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T)
      hs2
  have hpow :
      (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 4 ≤
        (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 4 := by
    exact pow_le_pow_left₀
      (by
        linarith [covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g P])
      (add_le_add le_rfl hPjet) 4
  have hC : H2Poly (I := I) (M := M) g T 1 Kc
      (lcvCurv (I := I) (M := M) g T) := by
    refine ⟨hKc, ?_⟩
    simpa only [pow_one] using hcurv T
  have hCs :=
    hp_raise (I := I) (M := M) g T (by omega : 1 ≤ 4)
      (hp_smul (I := I) (M := M) g T (-(s / 2) : ℝ) hC)
  have hscale : (-(s / 2) : ℝ) ^ 2 ≤ 1 := by
    nlinarith only [hs0, hs1]
  have hscaleK : (-(s / 2) : ℝ) ^ 2 * Kc ≤ Kc := by
    calc
      (-(s / 2) : ℝ) ^ 2 * Kc ≤ 1 * Kc :=
        mul_le_mul_of_nonneg_right hscale hKc
      _ = Kc := one_mul Kc
  have hA : H2Poly (I := I) (M := M) g T 4 Kc
      ((-(s / 2) : ℝ) • lcvCurv (I := I) (M := M) g T) := by
    refine ⟨hKc, le_trans hCs.2 ?_⟩
    exact mul_le_mul_of_nonneg_right hscaleK
      (pow_nonneg
        (by
          linarith [covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T]) 4)
  have hQ : H2Poly (I := I) (M := M) g T 4 Kq
      (lcvQuad (I := I) (M := M) g gm) := by
    refine ⟨hKq, ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (lcvQuad (I := I) (M := M) g gm) ≤
        Kq * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 4 :=
          hquad gm P hP htie hδ_le hδ0 hδP
      _ ≤ Kq * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 4 :=
        mul_le_mul_of_nonneg_left hpow hKq
  have hSub := hp_sub (I := I) (M := M) g T hA hQ
  simpa only [lcvR4, gm, K] using hSub.2

private theorem lcvR4_h2_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lcvR4 (I := I) (M := M) g T hδ hδZ s) ≤
        (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨Kc, hKc, hcurv⟩ :=
    lcvCurv_h2_lin (I := I) (M := M) hDim g
  obtain ⟨Dq, hDq, hquad⟩ :=
    lcvQuad_h2_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  let Z : ℝ → ℝ := fun R => 2 * (Kc + (Dq R) ^ 2)
  let D : ℝ → ℝ := fun R => Real.sqrt (Z R)
  have hZ : ∀ R : ℝ, 0 ≤ Z R :=
    fun R => mul_nonneg (by norm_num)
      (add_nonneg hKc (sq_nonneg _))
  refine ⟨D, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3 s hs
  obtain ⟨hs0, hs1⟩ := hs
  let P : SmoothCcTensor g 0 2 := s • T
  let gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδ hδZ s
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt ⟨hs0, hs1⟩
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    rw [← show convexPerturbation (I := I) g T 0 s = P by
      simp only [P, convexPerturbation, smul_zero, zero_add]]
    exact metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hδ hδZ hs_mem x u v
  have hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [P, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδ hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs0]
      ring
    simpa only [P, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith only [hs0, hs1]
  have hP2 :
      covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [show P = s • T by rfl, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T)
      hs2).trans hT2
  have hP3 :
      covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [show P = s • T by rfl, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T)
      hs2).trans hT3
  have hT2A :
      covariantJetNormSq (I := I) (M := M) g 2 T ≤ A ^ 2 :=
    (covariantJetNormSq_mono (I := I) (M := M) g (by omega) T).trans hT3
  have hCurv :
      covariantJetNormSq (I := I) (M := M) g 2
          (lcvCurv (I := I) (M := M) g T) ≤
        Kc * A ^ 2 :=
    (hcurv T).trans
      (mul_le_mul_of_nonneg_left hT2A hKc)
  have hscale : (-(s / 2) : ℝ) ^ 2 ≤ 1 := by
    nlinarith only [hs0, hs1]
  have hScaled :
      covariantJetNormSq (I := I) (M := M) g 2
          ((-(s / 2) : ℝ) •
            lcvCurv (I := I) (M := M) g T) ≤
        Kc * A ^ 2 := by
    rw [covariantJetNormSq_smul]
    calc
      (-(s / 2) : ℝ) ^ 2 *
          covariantJetNormSq (I := I) (M := M) g 2
            (lcvCurv (I := I) (M := M) g T) ≤
        (-(s / 2) : ℝ) ^ 2 * (Kc * A ^ 2) :=
          mul_le_mul_of_nonneg_left hCurv (sq_nonneg _)
      _ ≤ 1 * (Kc * A ^ 2) :=
        mul_le_mul_of_nonneg_right hscale
          (mul_nonneg hKc (sq_nonneg _))
      _ = Kc * A ^ 2 := one_mul _
  have hQuad :
      covariantJetNormSq (I := I) (M := M) g 2
          (lcvQuad (I := I) (M := M) g gm) ≤
        (Dq R * A ^ 2) ^ 2 :=
    hquad gm P hP htie hδ_le hδ0 hδP
      R A hR hA hP2 hP3
  let X : ℝ := A + A ^ 2
  have hA3 : 0 ≤ A * A ^ 2 :=
    mul_nonneg hA (sq_nonneg A)
  have hA2X : A ^ 2 ≤ X ^ 2 := by
    simp only [X]
    nlinarith only [sq_nonneg A, hA3]
  have hA4X : A ^ 4 ≤ X ^ 2 := by
    simp only [X]
    nlinarith only [sq_nonneg A, hA3]
  have hdom :
      2 * (Kc * A ^ 2 + (Dq R * A ^ 2) ^ 2) ≤
        Z R * X ^ 2 := by
    have hc :=
      mul_le_mul_of_nonneg_left hA2X hKc
    have hq :=
      mul_le_mul_of_nonneg_left hA4X (sq_nonneg (Dq R))
    simp only [Z]
    nlinarith only [hc, hq]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (lcvR4 (I := I) (M := M) g T hδ hδZ s) ≤
      2 * (covariantJetNormSq (I := I) (M := M) g 2
          ((-(s / 2) : ℝ) •
            lcvCurv (I := I) (M := M) g T) +
        covariantJetNormSq (I := I) (M := M) g 2
          (lcvQuad (I := I) (M := M) g gm)) := by
            simpa only [lcvR4, gm] using
              covariantJetNormSq_sub_le (I := I) (M := M) g 2
                ((-(s / 2) : ℝ) •
                  lcvCurv (I := I) (M := M) g T)
                (lcvQuad (I := I) (M := M) g gm)
    _ ≤ 2 * (Kc * A ^ 2 + (Dq R * A ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hScaled hQuad) (by norm_num)
    _ ≤ Z R * X ^ 2 := hdom
    _ = (D R * (A + A ^ 2)) ^ 2 := by
      have hsqrt : (Real.sqrt (Z R)) ^ 2 = Z R :=
        Real.sq_sqrt (hZ R)
      simp only [D, X, mul_pow, hsqrt]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit sigmaCompactSpace in
private theorem edgePair_eq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
        lieDecompositionQ lieDecompositionEps s =
      deTurckLieCovariantDerivativeDecompositionPairTraceFamily (I := I) (M := M)
        g T hδ hδZ
          ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
            Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
              Equiv.swap (0 : Fin 4) 1,
            Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
          ![(-1 : ℝ), -1, 1] s := by
  rfl

private theorem lieCov_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {s : ℝ} (_hs : s ∈ Set.Icc (0 : ℝ) 1),
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
              lieDecompositionQ lieDecompositionEps s) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 6 := by
  obtain ⟨Kp, hKp, hpair⟩ :=
    lcvPair_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Kr, hKr, hr4⟩ :=
    lcvR4_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 6 2
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := Ca * Kp * (fr * (fr * Kr))
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K :=
    mul_nonneg (mul_nonneg hCa hKp)
      (mul_nonneg hfr (mul_nonneg hfr hKr))
  refine ⟨K, hK, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ s hs
  let P : SmoothCcTensor g 0 2 :=
    convexPerturbation (I := I) g T 0 s
  let gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδ hδZ s
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v :=
    fun x u v => metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hδ hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    convert convexPerturbation_gFibreOpBound
      (I := I) (M := M) g T 0 hδ hδZ hs.1 hs.2 using 1
    all_goals ring
  have hcP : P = s • T := by
    simp only [P, convexPerturbation, smul_zero, zero_add]
  have hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    rw [hcP]
    simp only [ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith only [hs.1, hs.2]
  have hPjet :
      covariantJetNormSq (I := I) (M := M) g 3 P ≤
        covariantJetNormSq (I := I) (M := M) g 3 T := by
    rw [hcP, covariantJetNormSq_smul]
    exact mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T) hs2
  have hpow :
      (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 2 ≤
        (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 2 := by
    exact pow_le_pow_left₀
      (by
        linarith [covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g P])
      (add_le_add le_rfl hPjet) 2
  have hPair : H2Poly (I := I) (M := M) g T 2 Kp
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm) := by
    refine ⟨hKp, ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm) ≤
        Kp * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 2 :=
          hpair gm P hP htie hδ_le hδ0 hδP
      _ ≤ Kp * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 2 :=
        mul_le_mul_of_nonneg_left hpow hKp
  have hR4 : H2Poly (I := I) (M := M) g T 4 Kr
      (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδ hδZ s) := by
    refine ⟨hKr, ?_⟩
    rw [lcvR4_eq (I := I) (M := M) g T hδ hδZ s]
    exact hr4 T hT hδ_le hδ0 hδ hδZ hs
  have hSlot :=
    hp_slot2 (I := I) (M := M) g T hR4
  have hPerm :=
    hp_rsperm (I := I) (M := M) g T deTurckLieCovariantDerivativePairTracePermutation hSlot
  have hApp :=
    hp_app_of (I := I) (M := M) g T Ca hCa
      (happ (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδ hδZ s))))
      hPair hPerm
  have hNeg :=
    hp_smul (I := I) (M := M) g T (-1 : ℝ) hApp
  rw [edgePair_eq (I := I) (M := M) g T hδ hδZ s]
  rw [lieCov_residual (I := I) (M := M)
    g T hδ_lt hδ hδZ hT hs]
  simpa only [K, fr, gm, Nat.reduceAdd, neg_sq, one_pow, one_mul]
    using hNeg.2

private theorem lieCov_h2_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
              lieDecompositionQ lieDecompositionEps s) ≤
        (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨Bp, hBp, hpair⟩ :=
    lcvPair_h2_low (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Dr, hDr, hr4⟩ :=
    lcvR4_h2_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 6 2
  let fr : ℝ := Module.finrank ℝ E
  let Z : ℝ → ℝ := fun R =>
    Ca * Bp R * (fr * (fr * (Dr R) ^ 2))
  let D : ℝ → ℝ := fun R => Real.sqrt (Z R)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨D, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3 s hs
  let P : SmoothCcTensor g 0 2 :=
    convexPerturbation (I := I) g T 0 s
  let gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδ hδZ s
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v :=
    fun x u v => metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hδ hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    convert convexPerturbation_gFibreOpBound
      (I := I) (M := M) g T 0 hδ hδZ hs.1 hs.2 using 1
    all_goals ring
  have hcP : P = s • T := by
    simp only [P, convexPerturbation, smul_zero, zero_add]
  have hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    rw [hcP]
    simp only [ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith only [hs.1, hs.2]
  have hP2 :
      covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T)
      hs2).trans hT2
  have hPair : H2Poly (I := I) (M := M) g T 0 (Bp R)
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm) := by
    refine ⟨hBp R hR, ?_⟩
    simpa only [pow_zero, mul_one] using
      hpair gm P hP htie hδ_le hδ0 hδP R hR hP2
  have hR4 : H2Poly (I := I) (M := M) g T 0
      ((Dr R * (A + A ^ 2)) ^ 2)
      (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδ hδZ s) := by
    refine ⟨sq_nonneg _, ?_⟩
    rw [lcvR4_eq (I := I) (M := M) g T hδ hδZ s]
    simpa only [pow_zero, mul_one] using
      hr4 T hT hδ_le hδ0 hδ hδZ
        R A hR hA hT2 hT3 hs
  have hSlot :=
    hp_slot2 (I := I) (M := M) g T hR4
  have hPerm :=
    hp_rsperm (I := I) (M := M) g T deTurckLieCovariantDerivativePairTracePermutation hSlot
  have hApp :=
    hp_app_of (I := I) (M := M) g T Ca hCa
      (happ (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδ hδZ s))))
      hPair hPerm
  have hNeg :=
    hp_smul (I := I) (M := M) g T (-1 : ℝ) hApp
  have hZR : 0 ≤ Z R := by
    exact mul_nonneg
      (mul_nonneg hCa (hBp R hR))
      (mul_nonneg hfr
        (mul_nonneg hfr (sq_nonneg _)))
  rw [edgePair_eq (I := I) (M := M) g T hδ hδZ s]
  rw [lieCov_residual (I := I) (M := M)
    g T hδ_lt hδ hδZ hT hs]
  calc
    _ ≤ (-1 : ℝ) ^ 2 *
        (Ca * Bp R *
          (fr * (fr * (Dr R * (A + A ^ 2)) ^ 2))) *
        (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 0 := hNeg.2
    _ = (D R * (A + A ^ 2)) ^ 2 := by
      have hsqrt : (Real.sqrt (Z R)) ^ 2 = Z R :=
        Real.sq_sqrt hZR
      simp only [D, Z, pow_zero, mul_one, neg_sq, one_pow,
        mul_pow, hsqrt]
      ring

private theorem lieCov_act_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T W : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g
                (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g -
              deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
                lieDecompositionQ lieDecompositionEps s) W) ≤
        (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨Bl, hBl, hlie⟩ :=
    lieCov_h2_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 2 2
  let C : ℝ := Real.sqrt Ca
  let D : ℝ → ℝ := fun R => C * Bl R * R
  refine ⟨D, fun R hR =>
    mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (hBl R hR)) hR, ?_⟩
  intro T W hT δ hδ_le hδ0 hδ hδZ
    R A hR hA hT2 hT3 hW2 s hs
  let Φ : SmoothCcTensor g 2 2 :=
    deTurckLieCovariantDerivativeArmField (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g -
      deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
        lieDecompositionQ lieDecompositionEps s
  have hΦ :
      covariantJetNormSq (I := I) (M := M) g 2 Φ ≤
        (Bl R * (A + A ^ 2)) ^ 2 :=
    hlie T hT hδ_le hδ0 hδ hδZ
      R A hR hA hT2 hT3 hs
  have hW0 :
      0 ≤ covariantJetNormSq (I := I) (M := M) g 2 W :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g W
  have hraw :
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2 Φ W) ≤
        Ca * (Bl R * (A + A ^ 2)) ^ 2 * R ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2 Φ W) ≤
        Ca * covariantJetNormSq (I := I) (M := M) g 2 Φ *
          covariantJetNormSq (I := I) (M := M) g 2 W := by
            simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using happ Φ W
      _ ≤ Ca * (Bl R * (A + A ^ 2)) ^ 2 * R ^ 2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hΦ hCa) hW2 hW0
          (mul_nonneg hCa (sq_nonneg _))
  change covariantJetNormSq (I := I) (M := M) g 2
      (operatorFieldApply (I := I) (M := M) g 2 2 Φ W) ≤ _
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2 Φ W) ≤
      Ca * (Bl R * (A + A ^ 2)) ^ 2 * R ^ 2 := hraw
    _ = (D R * (A + A ^ 2)) ^ 2 := by
      rw [show Ca = C ^ 2 by
        simpa only [C] using (Real.sq_sqrt hCa).symm]
      simp only [D]
      ring

omit sigmaCompactSpace in
private theorem selfBase_decomp
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    pathIntegrand (I := I) (M := M) g g T hδ hδZ s =
      let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
      ((((-2 : ℝ) • symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm (s • T) +
          (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g gm g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
              lieDecompositionQ lieDecompositionEps s)) +
        lieCorrectionZeroVectorBundle (I := I) (M := M) g gm) +
        lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g) +
        lieCorrectionZeroRiemann (I := I) (M := M) g gm := by
  rw [rhsSelf_good (I := I) (M := M)
    g g T hT hδ_lt hδ hδZ hs]
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  let Q := deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
    lieDecompositionQ lieDecompositionEps s
  have hlie := lieLow_decomp (I := I) (M := M) g gm g Q
  calc
    _ = (-2 : ℝ) • symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm (s • T) +
        (deTurckLieCoeffField (I := I) (M := M) g gm g +
          lieCorrectionZeroField (I := I) (M := M) g gm g - Q) := by
      simp only [gm, Q]
      abel
    _ = (-2 : ℝ) • symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm (s • T) +
        ((deTurckLieCovariantDerivativeArmField (I := I) (M := M) g gm g - Q) +
          (deTurckLieEndoArmField (I := I) (M := M) g gm g -
            deTurckLieEndoArmField (I := I) (M := M) g gm g) +
          ((((lieCorrectionZeroInsertion (I := I) (M := M) g gm g -
                lieCorrectionZeroInsertion (I := I) (M := M) g gm g) +
              lieCorrectionZeroVectorBundle (I := I) (M := M) g gm) +
            lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g) +
          lieCorrectionZeroRiemann (I := I) (M := M) g gm)) := by
      rw [hlie]
    _ = _ := by
      simp only [sub_self, zero_add, add_zero]
      abel

private theorem rhsSelf_act_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (pathIntegrand (I := I) (M := M) g g T hδ hδZ s) T) ≤
        (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨Dr, hDr, hric⟩ :=
    ricciGood_act_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Dl, hDl, hlie⟩ :=
    lieCov_act_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Dv, hDv, hvb⟩ :=
    lieCorrectionZeroVB_act_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Da, hDa, hamix⟩ :=
    lieCorrectionZeroMixedConnection_act_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Dc, hDc, hriem⟩ :=
    lieCorrectionZeroRiem_act_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  let Kr : ℝ → ℝ := fun R => (Dr R) ^ 2
  let Kl : ℝ → ℝ := fun R => (Dl R) ^ 2
  let Kv : ℝ → ℝ := fun R => (Dv R) ^ 2
  let Ka : ℝ → ℝ := fun R => (Da R) ^ 2
  let Kc : ℝ := Dc ^ 2
  let Krs : ℝ → ℝ := fun R => (-2 : ℝ) ^ 2 * Kr R
  let K₂ : ℝ → ℝ := fun R => 2 * (Krs R + Kl R)
  let K₃ : ℝ → ℝ := fun R => 2 * (K₂ R + Kv R)
  let K₄ : ℝ → ℝ := fun R => 2 * (K₃ R + Ka R)
  let K : ℝ → ℝ := fun R => 2 * (K₄ R + Kc)
  let D : ℝ → ℝ := fun R => Real.sqrt (K R)
  have hKr : ∀ R : ℝ, 0 ≤ Kr R := fun R => sq_nonneg _
  have hKl : ∀ R : ℝ, 0 ≤ Kl R := fun R => sq_nonneg _
  have hKv : ∀ R : ℝ, 0 ≤ Kv R := fun R => sq_nonneg _
  have hKa : ∀ R : ℝ, 0 ≤ Ka R := fun R => sq_nonneg _
  have hKc : 0 ≤ Kc := sq_nonneg _
  have hKrs : ∀ R : ℝ, 0 ≤ Krs R :=
    fun R => mul_nonneg (sq_nonneg _) (hKr R)
  have hK₂ : ∀ R : ℝ, 0 ≤ K₂ R :=
    fun R => mul_nonneg (by norm_num)
      (add_nonneg (hKrs R) (hKl R))
  have hK₃ : ∀ R : ℝ, 0 ≤ K₃ R :=
    fun R => mul_nonneg (by norm_num)
      (add_nonneg (hK₂ R) (hKv R))
  have hK₄ : ∀ R : ℝ, 0 ≤ K₄ R :=
    fun R => mul_nonneg (by norm_num)
      (add_nonneg (hK₃ R) (hKa R))
  have hK : ∀ R : ℝ, 0 ≤ K R :=
    fun R => mul_nonneg (by norm_num)
      (add_nonneg (hK₄ R) hKc)
  refine ⟨D, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3 s hs
  let P : SmoothCcTensor g 0 2 := s • T
  let gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδ hδZ s
  let X : ℝ := A + A ^ 2
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    rw [← show convexPerturbation (I := I) g T 0 s = P by
      simp only [P, convexPerturbation, smul_zero, zero_add]]
    exact metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hδ hδZ hs_mem x u v
  have hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [P, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδ hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [P, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith only [hs.1, hs.2]
  have hP2 :
      covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [show P = s • T by rfl, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T)
      hs2).trans hT2
  have hP3 :
      covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [show P = s • T by rfl, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T)
      hs2).trans hT3
  have hT2A :
      covariantJetNormSq (I := I) (M := M) g 2 T ≤ A ^ 2 :=
    (covariantJetNormSq_mono (I := I) (M := M) g (by omega) T).trans hT3
  have hA2X : A ^ 2 ≤ X := by
    simp only [X]
    linarith
  have reweight {r s : ℕ} {S : SmoothCcTensor g r s}
      {U V : ℝ} (hUV : U = V)
      (hS : H2Poly (I := I) (M := M) g T 0 U S) :
      H2Poly (I := I) (M := M) g T 0 V S := by
    rwa [← hUV]
  let Ric : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2
      (symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P) T
  have hRic0 : H2Poly (I := I) (M := M) g T 0
      ((Dr R * X) ^ 2) Ric := by
    refine ⟨sq_nonneg _, ?_⟩
    simpa only [Ric, X, pow_zero, mul_one] using
      hric gm P T hP hT htie hδ_le hδ0 hδP
        R A hR hA hP2 hP3 hT2
  have hrEq : (Dr R * X) ^ 2 = Kr R * X ^ 2 := by
    simp only [Kr]
    ring
  have hRic := reweight hrEq hRic0
  let Lie : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2
      (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g gm g -
        deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
          lieDecompositionQ lieDecompositionEps s) T
  have hLie0 : H2Poly (I := I) (M := M) g T 0
      ((Dl R * X) ^ 2) Lie := by
    refine ⟨sq_nonneg _, ?_⟩
    simpa only [Lie, gm, X, pow_zero, mul_one] using
      hlie T T hT hδ_le hδ0 hδ hδZ
        R A hR hA hT2 hT3 hT2 hs
  have hlEq : (Dl R * X) ^ 2 = Kl R * X ^ 2 := by
    simp only [Kl]
    ring
  have hLie := reweight hlEq hLie0
  let VB : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2
      (lieCorrectionZeroVectorBundle (I := I) (M := M) g gm) T
  have hVBraw :=
    hvb gm P T hP htie hδ_le hδ0 hδP
      R A hR hA hP2 hP3 hT2
  have hVBmono :
      (Dv R * A ^ 2) ^ 2 ≤ (Dv R * X) ^ 2 :=
    pow_le_pow_left₀
      (mul_nonneg (hDv R hR) (sq_nonneg A))
      (mul_le_mul_of_nonneg_left hA2X (hDv R hR)) 2
  have hVB0 : H2Poly (I := I) (M := M) g T 0
      ((Dv R * X) ^ 2) VB := by
    refine ⟨sq_nonneg _, ?_⟩
    simpa only [VB, pow_zero, mul_one] using
      hVBraw.trans hVBmono
  have hvEq : (Dv R * X) ^ 2 = Kv R * X ^ 2 := by
    simp only [Kv]
    ring
  have hVB := reweight hvEq hVB0
  let AMix : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2
      (lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g) T
  have hAMixRaw :=
    hamix gm P T hP htie hδ_le hδ0 hδP
      R A hR hA hP2 hP3 hT2
  have hAMixMono :
      (Da R * A ^ 2) ^ 2 ≤ (Da R * X) ^ 2 :=
    pow_le_pow_left₀
      (mul_nonneg (hDa R hR) (sq_nonneg A))
      (mul_le_mul_of_nonneg_left hA2X (hDa R hR)) 2
  have hAMix0 : H2Poly (I := I) (M := M) g T 0
      ((Da R * X) ^ 2) AMix := by
    refine ⟨sq_nonneg _, ?_⟩
    simpa only [AMix, pow_zero, mul_one] using
      hAMixRaw.trans hAMixMono
  have haEq : (Da R * X) ^ 2 = Ka R * X ^ 2 := by
    simp only [Ka]
    ring
  have hAMix := reweight haEq hAMix0
  let Riem : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2
      (lieCorrectionZeroRiemann (I := I) (M := M) g gm) T
  have hRiem0 : H2Poly (I := I) (M := M) g T 0
      ((Dc * X) ^ 2) Riem := by
    refine ⟨sq_nonneg _, ?_⟩
    simpa only [Riem, X, pow_zero, mul_one] using
      hriem gm P T hP htie hδ_le hδ0 hδP
        A hA hP3 hT2A
  have hcEq : (Dc * X) ^ 2 = Kc * X ^ 2 := by
    simp only [Kc]
    ring
  have hRiem := reweight hcEq hRiem0
  have hRicS0 :=
    hp_smul (I := I) (M := M) g T (-2 : ℝ) hRic
  have hrsEq :
      (-2 : ℝ) ^ 2 * (Kr R * X ^ 2) =
        Krs R * X ^ 2 := by
    simp only [Krs]
    ring
  have hRicS := reweight hrsEq hRicS0
  have h12eq :
      2 * (Krs R * X ^ 2 + Kl R * X ^ 2) =
        K₂ R * X ^ 2 := by
    simp only [K₂]
    ring
  have h12 := reweight h12eq
    (hp_add (I := I) (M := M) g T hRicS hLie)
  have h123eq :
      2 * (K₂ R * X ^ 2 + Kv R * X ^ 2) =
        K₃ R * X ^ 2 := by
    simp only [K₃]
    ring
  have h123 := reweight h123eq
    (hp_add (I := I) (M := M) g T h12 hVB)
  have h1234eq :
      2 * (K₃ R * X ^ 2 + Ka R * X ^ 2) =
        K₄ R * X ^ 2 := by
    simp only [K₄]
    ring
  have h1234 := reweight h1234eq
    (hp_add (I := I) (M := M) g T h123 hAMix)
  have h12345eq :
      2 * (K₄ R * X ^ 2 + Kc * X ^ 2) =
        K R * X ^ 2 := by
    simp only [K]
    ring
  have h12345 := reweight h12345eq
    (hp_add (I := I) (M := M) g T h1234 hRiem)
  have hraw :
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (pathIntegrand (I := I) (M := M) g g T hδ hδZ s) T) ≤
        K R * X ^ 2 := by
    rw [selfBase_decomp (I := I) (M := M)
      g T hT hδ_lt hδ hδZ hs]
    simpa only [gm, P, Ric, Lie, VB, AMix, Riem,
      operatorFieldApplication_add_left, operatorFieldApplication_smul_left, pow_zero, mul_one]
      using h12345.2
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2
          (pathIntegrand (I := I) (M := M) g g T hδ hδZ s) T) ≤
      K R * X ^ 2 := hraw
    _ = (D R * (A + A ^ 2)) ^ 2 := by
      have hsqrt : (Real.sqrt (K R)) ^ 2 = K R :=
        Real.sq_sqrt (hK R)
      simp only [D, X, mul_pow, hsqrt]

private theorem selfInt_act_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (selfLowInt (I := I) (M := M) g g T
              (lt_of_le_of_lt hδ_le hδ₀) hδ hδZ) T) ≤
        (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨D, hD, hcoeff⟩ :=
    rhsSelf_act_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  refine ⟨D, hD, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3
  let S : Set ℝ := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  let Φ : ℝ → SmoothCcTensor g 2 2 :=
    pathIntegrand (I := I) (M := M) g g T hδ hδZ
  let Ψ : ℝ → SmoothCcTensor g 0 2 :=
    fun s => ccOperatorFieldComp (I := I) (M := M) g 0 2 2 (Φ s) T
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hΦ : JointRS (I := I) g 2 2 S Φ := by
    have hraw := selfLow_joint (I := I) (M := M) g g T hδ hδZ
    rw [linearizedRicciThreeArmHjoint] at hraw
    exact hraw
  have hTjoint : JointRS (I := I) g 0 2 S (fun _ : ℝ => T) :=
    joint_const (I := I) g T
  have hΨ : JointRS (I := I) g 0 2 S Ψ := by
    simpa only [Ψ] using
      joint_app (I := I) (M := M) g Φ (fun _ : ℝ => T) hΦ hTjoint
  have hB : 0 ≤ D R * (A + A ^ 2) :=
    mul_nonneg (hD R hR) (add_nonneg hA (sq_nonneg A))
  have hpath := path_jetL2_le (I := I) (M := M) g 0 2 2
    Ψ S metricPerturbationPathDomain_isOpen hSI hΨ
    (fun s hs => by
      simpa only [Ψ, Φ, operatorFieldComposition_zero_eq_operatorFieldApply, covariantJetNormSq] using
        hcoeff T hT hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3 hs)
  have happ : JointRS (I := I) g 0 2 S
      (fun s => ccOperatorFieldComp (I := I) (M := M) g 0 2 2 (Φ s) T) := by
    simpa only [Ψ] using hΨ
  have hcomm := path_app_zero (I := I) (M := M) g Φ T S
    metricPerturbationPathDomain_isOpen hSI hΦ happ
  rw [hcomm] at hpath
  simpa only [selfLowInt, S, Φ, covariantJetNormSq] using hpath

private theorem curvC0_act_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (T : SmoothCcTensor g 0 2) (A : ℝ), 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (metricPrincipalDefectCurvCoeff (I := I) g g) T) ≤
        (D * (A + A ^ 2)) ^ 2 := by
  obtain ⟨C, hC, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 2 2
  let F : SmoothCcTensor g 2 2 :=
    metricPrincipalDefectCurvCoeff (I := I) g g
  let JF : ℝ := covariantJetNormSq (I := I) (M := M) g 2 F
  let K : ℝ := C * JF
  let D : ℝ := Real.sqrt K
  have hJF : 0 ≤ JF :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g F
  have hK : 0 ≤ K := mul_nonneg hC hJF
  refine ⟨D, Real.sqrt_nonneg _, ?_⟩
  intro T A hA hT3
  have hT2 :
      covariantJetNormSq (I := I) (M := M) g 2 T ≤ A ^ 2 :=
    (covariantJetNormSq_mono (I := I) (M := M) g (by omega) T).trans hT3
  have hX :
      A ^ 2 ≤ (A + A ^ 2) ^ 2 := by
    have hAX : A ≤ A + A ^ 2 := by nlinarith only [sq_nonneg A]
    exact pow_le_pow_left₀ hA hAX 2
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2
          (metricPrincipalDefectCurvCoeff (I := I) g g) T) ≤
      C * JF * covariantJetNormSq (I := I) (M := M) g 2 T := by
        simpa only [F, JF, operatorFieldComposition_zero_eq_operatorFieldApply] using happ F T
    _ ≤ C * JF * A ^ 2 :=
      mul_le_mul_of_nonneg_left hT2 hK
    _ ≤ K * (A + A ^ 2) ^ 2 := by
      simpa only [K] using mul_le_mul_of_nonneg_left hX hK
    _ = (D * (A + A ^ 2)) ^ 2 := by
      rw [mul_pow, show D ^ 2 = K by
        simpa only [D] using Real.sq_sqrt hK]

private theorem lowC0_act_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (lowerScaleActionCoefficients (I := I) (M := M) g g T
              (lt_of_le_of_lt hδ_le hδ₀) hδ hδZ).zeroOrderCoefficient T) ≤
        (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨Di, hDi, hint⟩ :=
    selfInt_act_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Df, hDf, hfixed⟩ :=
    curvC0_act_tame (I := I) (M := M) hDim g
  let K : ℝ → ℝ := fun R => 2 * (Di R ^ 2 + Df ^ 2)
  let D : ℝ → ℝ := fun R => Real.sqrt (K R)
  have hK : ∀ R : ℝ, 0 ≤ K R := fun R =>
    mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  refine ⟨D, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3
  let X : ℝ := A + A ^ 2
  let U : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2
      (selfLowInt (I := I) (M := M) g g T
        (lt_of_le_of_lt hδ_le hδ₀) hδ hδZ) T
  let V : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2
      (metricPrincipalDefectCurvCoeff (I := I) g g) T
  have hU :
      covariantJetNormSq (I := I) (M := M) g 2 U ≤ (Di R * X) ^ 2 := by
    simpa only [U, X] using
      hint T hT hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3
  have hV :
      covariantJetNormSq (I := I) (M := M) g 2 V ≤ (Df * X) ^ 2 := by
    simpa only [V, X] using hfixed T A hA hT3
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2
          (lowerScaleActionCoefficients (I := I) (M := M) g g T
            (lt_of_le_of_lt hδ_le hδ₀) hδ hδZ).zeroOrderCoefficient T) =
      covariantJetNormSq (I := I) (M := M) g 2 (U + V) := by
        simp only [lowerScaleActionCoefficients, operatorFieldApplication_add_left, U, V]
    _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 2 U +
        covariantJetNormSq (I := I) (M := M) g 2 V) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 2 U V
    _ ≤ 2 * ((Di R * X) ^ 2 + (Df * X) ^ 2) := by
      gcongr
    _ = (D R * X) ^ 2 := by
      have hDsq : (D R) ^ 2 = K R := by
        simpa only [D] using Real.sq_sqrt (hK R)
      simp only [mul_pow, hDsq, K]
      ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem grad_jet2
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (W : SmoothCcTensor g 0 s) :
    covariantJetNormSq (I := I) (M := M) g 2
        (iteratedCovGrad (I := I) g 0 s 1 W) ≤
      covariantJetNormSq (I := I) (M := M) g 3 W := by
  have h0 := iteratedCovGrad_comp_norm (I := I) (M := M) g s 1 0 W
  have h1 := iteratedCovGrad_comp_norm (I := I) (M := M) g s 1 1 W
  have h2 := iteratedCovGrad_comp_norm (I := I) (M := M) g s 1 2 W
  unfold covariantJetNormSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 h2 ⊢
  rw [h0, h1, h2]
  nlinarith only [sq_nonneg ‖W‖]

private theorem rhsOne_act_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (_hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 3 2
            (ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g T 0 hδ hδZ s)
            (iteratedCovGrad (I := I) g 0 2 1 T)) ≤
        (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨Br0, Br1, hBr0, hBr1, hric⟩ :=
    exists_linearizedRicciConnectionDifferenceOrderOneCoefficient_covariantJetNormSq_two_tame_bound (I := I) (M := M) hDim g hδ₀
  obtain ⟨Bl0, Bl1, hBl0, hBl1, hlie⟩ :=
    deTurckLieFirstOrder_h2_tame_bound (I := I) (M := M) hDim g g hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 3 2
  let C : ℝ := Real.sqrt Ca
  let B0 : ℝ → ℝ := fun R => 4 * Br0 R + 2 * Bl0 R
  let B1 : ℝ → ℝ := fun R => 4 * Br1 R + 2 * Bl1 R
  let D : ℝ → ℝ := fun R => C * (B0 R + B1 R)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hCsq : C ^ 2 = Ca := by
    simpa only [C] using Real.sq_sqrt hCa
  have hB0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R := by
    intro R hR
    exact add_nonneg
      (mul_nonneg (by norm_num) (hBr0 R hR))
      (mul_nonneg (by norm_num) (hBl0 R hR))
  have hB1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R := by
    intro R hR
    exact add_nonneg
      (mul_nonneg (by norm_num) (hBr1 R hR))
      (mul_nonneg (by norm_num) (hBl1 R hR))
  refine ⟨D, fun R hR =>
    mul_nonneg hC (add_nonneg (hB0 R hR) (hB1 R hR)), ?_⟩
  intro T δ hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3 s hs
  let P : SmoothCcTensor g 0 2 := s • T
  let gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδ hδZ s
  let Ar : ℝ := Br0 R + Br1 R * A
  let Al : ℝ := Bl0 R + Bl1 R * A
  let B : ℝ := 4 * Ar + 2 * Al
  let X : ℝ := A + A ^ 2
  let Φ : SmoothCcTensor g 3 2 :=
    ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g T 0 hδ hδZ s
  let W : SmoothCcTensor g 0 3 :=
    iteratedCovGrad (I := I) g 0 2 1 T
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    rw [← show convexPerturbation (I := I) g T 0 s = P by
      simp only [P, convexPerturbation, smul_zero, zero_add]]
    exact metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hδ hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδ hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [P, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith only [hs.1, hs.2]
  have hP2 :
      covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [show P = s • T by rfl, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T)
      hs2).trans hT2
  have hP3 :
      covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [show P = s • T by rfl, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T)
      hs2).trans hT3
  have hAr : 0 ≤ Ar :=
    add_nonneg (hBr0 R hR) (mul_nonneg (hBr1 R hR) hA)
  have hAl : 0 ≤ Al :=
    add_nonneg (hBl0 R hR) (mul_nonneg (hBl1 R hR) hA)
  have hRic :
      covariantJetNormSq (I := I) (M := M) g 2
          (linearizedRicciConnectionDifferenceOrder1CoeffField
            (I := I) (M := M) g gm) ≤ Ar ^ 2 := by
    simpa only [covariantJetNormSq, Ar] using
      hric gm P htie hδ_le hδ0 hδP R A hR hA hP2 hP3
  have hLie :
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieArm1Coeff (I := I) (M := M) g gm g) ≤ Al ^ 2 := by
    simpa only [covariantJetNormSq, Al] using
      hlie gm P htie hδ_le hδ0 hδP R A hR hA hP2 hP3
  have haux := rhs_one_coefficient_sobolev_two_bound (I := I) (M := M)
    g g T 0 hδ hδZ s Ar Al hRic hLie
  have hinside : 0 ≤ 2 * (4 * Ar ^ 2 + Al ^ 2) := by
    positivity
  have hΦ :
      covariantJetNormSq (I := I) (M := M) g 2 Φ ≤ B ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 Φ ≤
          2 * (4 * Ar ^ 2 + Al ^ 2) := by
        simpa only [Φ, covariantJetNormSq, Real.sq_sqrt hinside] using haux
      _ ≤ B ^ 2 := by
        simp only [B]
        nlinarith only [mul_nonneg hAr hAl, sq_nonneg Ar, sq_nonneg Al]
  have hW :
      covariantJetNormSq (I := I) (M := M) g 2 W ≤ A ^ 2 :=
    (grad_jet2 (I := I) (M := M) g T).trans hT3
  have hB : 0 ≤ B :=
    add_nonneg (mul_nonneg (by norm_num) hAr)
      (mul_nonneg (by norm_num) hAl)
  have hBA :
      B * A ≤ (B0 R + B1 R) * X := by
    simp only [B, Ar, Al, B0, B1, X]
    nlinarith only [hBr0 R hR, hBr1 R hR, hBl0 R hR, hBl1 R hR,
      mul_nonneg (hBr0 R hR) hA, mul_nonneg (hBr1 R hR) hA,
      mul_nonneg (hBl0 R hR) hA, mul_nonneg (hBl1 R hR) hA]
  have hBX : 0 ≤ (B0 R + B1 R) * X :=
    mul_nonneg (add_nonneg (hB0 R hR) (hB1 R hR))
      (add_nonneg hA (sq_nonneg A))
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 3 2 Φ W) ≤
      Ca * covariantJetNormSq (I := I) (M := M) g 2 Φ *
        covariantJetNormSq (I := I) (M := M) g 2 W := by
          simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using happ Φ W
    _ ≤ Ca * B ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2 W := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hΦ hCa)
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g W)
    _ ≤ Ca * B ^ 2 * A ^ 2 := by
      exact mul_le_mul_of_nonneg_left hW
        (mul_nonneg hCa (sq_nonneg B))
    _ = Ca * (B * A) ^ 2 := by ring
    _ ≤ Ca * ((B0 R + B1 R) * X) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg hB hA) hBA 2) hCa
    _ = (D R * X) ^ 2 := by
      simp only [D, mul_pow, hCsq]
      ring

private theorem oneInt_act_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 3 2
            (ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M) g g T 0
              (lt_of_le_of_lt hδ_le hδ₀) hδ
              (lt_of_le_of_lt hδ_le hδ₀) hδZ)
            (iteratedCovGrad (I := I) g 0 2 1 T)) ≤
        (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨D, hD, hcoeff⟩ :=
    rhsOne_act_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  refine ⟨D, hD, ?_⟩
  intro T δ hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3
  let S : Set ℝ := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  let Φ : ℝ → SmoothCcTensor g 3 2 :=
    ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g T 0 hδ hδZ
  let W : SmoothCcTensor g 0 3 :=
    iteratedCovGrad (I := I) g 0 2 1 T
  let Ψ : ℝ → SmoothCcTensor g 0 2 :=
    fun s => ccOperatorFieldComp (I := I) (M := M) g 0 3 2 (Φ s) W
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hΦ : JointRS (I := I) g 3 2 S Φ := by
    have hraw := ricciDeTurckRemainderFirstOrderCoefficient_path_joint
      (I := I) (M := M) g g T 0 hδ hδZ
    rw [linearizedRicciThreeArmHjoint] at hraw
    exact hraw
  have hWjoint : JointRS (I := I) g 0 3 S (fun _ : ℝ => W) :=
    joint_const (I := I) g W
  have hΨ : JointRS (I := I) g 0 2 S Ψ := by
    simpa only [Ψ] using
      joint_app (I := I) (M := M) g Φ (fun _ : ℝ => W) hΦ hWjoint
  have hB : 0 ≤ D R * (A + A ^ 2) :=
    mul_nonneg (hD R hR) (add_nonneg hA (sq_nonneg A))
  have hpath := path_jetL2_le (I := I) (M := M) g 0 2 2
    Ψ S metricPerturbationPathDomain_isOpen hSI hΨ
    (fun s hs => by
      simpa only [Ψ, Φ, W, operatorFieldComposition_zero_eq_operatorFieldApply, covariantJetNormSq] using
        hcoeff T hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3 hs)
  have happ : JointRS (I := I) g 0 2 S
      (fun s => ccOperatorFieldComp (I := I) (M := M) g 0 3 2 (Φ s) W) := by
    simpa only [Ψ] using hΨ
  have hcomm := path_app_zero (I := I) (M := M) g Φ W S
    metricPerturbationPathDomain_isOpen hSI hΦ happ
  rw [hcomm] at hpath
  simpa only [ricciDeTurckRemainderFirstOrderPathIntegral, S, Φ, W, covariantJetNormSq] using hpath

private theorem lowA1_act_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          ((lowerScaleActionCoefficients (I := I) (M := M) g g T
            (lt_of_le_of_lt hδ_le hδ₀) hδ hδZ).firstOrderAction
              (I := I) (M := M) T) ≤
        (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨D0, hD0, hzero⟩ :=
    lowC0_act_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨D1, hD1, hone⟩ :=
    oneInt_act_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  let K : ℝ → ℝ := fun R => 2 * (D0 R ^ 2 + D1 R ^ 2)
  let D : ℝ → ℝ := fun R => Real.sqrt (K R)
  have hK : ∀ R : ℝ, 0 ≤ K R := fun R =>
    mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  refine ⟨D, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3
  let X : ℝ := A + A ^ 2
  let Y0 : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2
      (lowerScaleActionCoefficients (I := I) (M := M) g g T
        (lt_of_le_of_lt hδ_le hδ₀) hδ hδZ).zeroOrderCoefficient T
  let Y1 : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 3 2
      (lowerScaleActionCoefficients (I := I) (M := M) g g T
        (lt_of_le_of_lt hδ_le hδ₀) hδ hδZ).firstOrderCoefficient
      (iteratedCovGrad (I := I) g 0 2 1 T)
  have hY0 :
      covariantJetNormSq (I := I) (M := M) g 2 Y0 ≤ (D0 R * X) ^ 2 := by
    simpa only [Y0, X] using
      hzero T hT hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3
  have hY1 :
      covariantJetNormSq (I := I) (M := M) g 2 Y1 ≤ (D1 R * X) ^ 2 := by
    simpa only [Y1, lowerScaleActionCoefficients, X] using
      hone T hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3
  change covariantJetNormSq (I := I) (M := M) g 2 (Y0 + Y1) ≤ _
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (Y0 + Y1) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 Y0 +
          covariantJetNormSq (I := I) (M := M) g 2 Y1) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 2 Y0 Y1
    _ ≤ 2 * ((D0 R * X) ^ 2 + (D1 R * X) ^ 2) := by
      gcongr
    _ = (D R * X) ^ 2 := by
      have hDsq : (D R) ^ 2 = K R := by
        simpa only [D] using Real.sq_sqrt (hK R)
      simp only [mul_pow, hDsq, K]
      ring

private theorem rhsSelf_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {s : ℝ} (_hs : s ∈ Set.Icc (0 : ℝ) 1),
      covariantJetNormSq (I := I) (M := M) g 2
          (pathIntegrand (I := I) (M := M) g g T hδ hδZ s) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 6 := by
  obtain ⟨Kr, hKr, hricci⟩ :=
    ricciGood_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Kl, hKl, hlie⟩ :=
    lieCov_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Kv, hKv, hvb⟩ :=
    lieCorrectionZeroVB_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ka, hKa, hamix⟩ :=
    lieCorrectionZeroMixedConnection_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Kc, hKc, hriem⟩ :=
    lieCorrectionZeroRiem_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  let Krs : ℝ := (-2 : ℝ) ^ 2 * Kr
  let K₂ : ℝ := 2 * (Krs + Kl)
  let K₃ : ℝ := 2 * (K₂ + Kv)
  let K₄ : ℝ := 2 * (K₃ + Ka)
  let K : ℝ := 2 * (K₄ + Kc)
  have hKrs : 0 ≤ Krs := mul_nonneg (sq_nonneg _) hKr
  have hK₂ : 0 ≤ K₂ :=
    mul_nonneg (by norm_num) (add_nonneg hKrs hKl)
  have hK₃ : 0 ≤ K₃ :=
    mul_nonneg (by norm_num) (add_nonneg hK₂ hKv)
  have hK₄ : 0 ≤ K₄ :=
    mul_nonneg (by norm_num) (add_nonneg hK₃ hKa)
  have hK : 0 ≤ K :=
    mul_nonneg (by norm_num) (add_nonneg hK₄ hKc)
  refine ⟨K, hK, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ s hs
  let P : SmoothCcTensor g 0 2 := s • T
  let gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδ hδZ s
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    rw [← show convexPerturbation (I := I) g T 0 s = P by
      simp only [P, convexPerturbation, smul_zero, zero_add]]
    exact metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hδ hδZ hs_mem x u v
  have hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [P, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδ hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [P, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith only [hs.1, hs.2]
  have hPjet :
      covariantJetNormSq (I := I) (M := M) g 3 P ≤
        covariantJetNormSq (I := I) (M := M) g 3 T := by
    rw [show P = s • T by rfl, covariantJetNormSq_smul]
    exact mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T) hs2
  have hpow (n : ℕ) :
      (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ n ≤
        (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ n := by
    exact pow_le_pow_left₀
      (by
        linarith [covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g P])
      (add_le_add le_rfl hPjet) n
  have hRic : H2Poly (I := I) (M := M) g T 3 Kr
      (symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P) := by
    refine ⟨hKr, ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P) ≤
        Kr * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 3 :=
          hricci gm P hP htie hδ_le hδ0 hδP
      _ ≤ Kr * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 3 :=
        mul_le_mul_of_nonneg_left (hpow 3) hKr
  have hRic6 :=
    hp_raise (I := I) (M := M) g T (by omega : 3 ≤ 6) hRic
  have hRicS :=
    hp_smul (I := I) (M := M) g T (-2 : ℝ) hRic6
  have hLie : H2Poly (I := I) (M := M) g T 6 Kl
      (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g gm g -
        deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
          lieDecompositionQ lieDecompositionEps s) :=
    ⟨hKl, hlie T hT hδ_le hδ0 hδ hδZ hs⟩
  have hVB : H2Poly (I := I) (M := M) g T 5 Kv
      (lieCorrectionZeroVectorBundle (I := I) (M := M) g gm) := by
    refine ⟨hKv, ?_⟩
    exact le_trans (hvb gm P hP htie hδ_le hδ0 hδP)
      (mul_le_mul_of_nonneg_left (hpow 5) hKv)
  have hVB6 :=
    hp_raise (I := I) (M := M) g T (by omega : 5 ≤ 6) hVB
  have hAMix : H2Poly (I := I) (M := M) g T 5 Ka
      (lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g) := by
    refine ⟨hKa, ?_⟩
    exact le_trans (hamix gm P hP htie hδ_le hδ0 hδP)
      (mul_le_mul_of_nonneg_left (hpow 5) hKa)
  have hAMix6 :=
    hp_raise (I := I) (M := M) g T (by omega : 5 ≤ 6) hAMix
  have hRiem : H2Poly (I := I) (M := M) g T 1 Kc
      (lieCorrectionZeroRiemann (I := I) (M := M) g gm) := by
    refine ⟨hKc, ?_⟩
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroRiemann (I := I) (M := M) g gm) ≤
        Kc * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) :=
          hriem gm P hP htie hδ_le hδ0 hδP
      _ ≤ Kc * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl hPjet) hKc
      _ = Kc * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 1 := by
        rw [pow_one]
  have hRiem6 :=
    hp_raise (I := I) (M := M) g T (by omega : 1 ≤ 6) hRiem
  have h12 := hp_add (I := I) (M := M) g T hRicS hLie
  have h123 := hp_add (I := I) (M := M) g T h12 hVB6
  have h1234 := hp_add (I := I) (M := M) g T h123 hAMix6
  have h12345 := hp_add (I := I) (M := M) g T h1234 hRiem6
  rw [selfBase_decomp (I := I) (M := M)
    g T hT hδ_lt hδ hδZ hs]
  simpa only [gm, P, Krs, K₂, K₃, K₄, K] using h12345.2

private theorem selfInt_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (selfLowInt (I := I) (M := M) g g T
            (lt_of_le_of_lt hδ_le hδ₀) hδ hδZ) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 6 := by
  obtain ⟨K, hK, hcoeff⟩ :=
    rhsSelf_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  refine ⟨K, hK, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ
  let X : ℝ :=
    K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 6
  have hX : 0 ≤ X := by
    exact mul_nonneg hK (pow_nonneg (by
      linarith [covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T]) 6)
  have hsX : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hpath := path_jetL2_le (I := I) (M := M) g 2 2 2
    (pathIntegrand (I := I) (M := M) g g T hδ hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen hSI
    (selfLow_joint (I := I) (M := M) g g T hδ hδZ)
    (fun s hs => by
      rw [hsX]
      simpa only [covariantJetNormSq, X] using
        hcoeff T hT hδ_le hδ0 hδ hδZ hs)
  rw [hsX] at hpath
  simpa only [selfLowInt, covariantJetNormSq, X] using hpath

private theorem lowC0_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (lowerScaleActionCoefficients (I := I) (M := M) g g T
            (lt_of_le_of_lt hδ_le hδ₀) hδ hδZ).zeroOrderCoefficient ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 6 := by
  obtain ⟨Ki, hKi, hint⟩ :=
    selfInt_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  let F : SmoothCcTensor g 2 2 :=
    metricPrincipalDefectCurvCoeff (I := I) g g
  let Kf : ℝ := covariantJetNormSq (I := I) (M := M) g 2 F
  let K : ℝ := 2 * (Ki + Kf)
  have hKf : 0 ≤ Kf :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g F
  have hK : 0 ≤ K :=
    mul_nonneg (by norm_num) (add_nonneg hKi hKf)
  refine ⟨K, hK, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ
  have hInt : H2Poly (I := I) (M := M) g T 6 Ki
      (selfLowInt (I := I) (M := M) g g T
        (lt_of_le_of_lt hδ_le hδ₀) hδ hδZ) :=
    ⟨hKi, hint T hT hδ_le hδ0 hδ hδZ⟩
  have hFixed0 := hp_const (I := I) (M := M) g T F
  have hFixed :=
    hp_raise (I := I) (M := M) g T (by omega : 0 ≤ 6) hFixed0
  have hsum := hp_add (I := I) (M := M) g T hInt hFixed
  simpa only [lowerScaleActionCoefficients, F, Kf, K] using hsum.2

omit [CompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem hp_weaken
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s n : ℕ} {A B : ℝ} {S : SmoothCcTensor g r s}
    (hAB : A ≤ B)
    (hS : H2Poly (I := I) (M := M) g P n A S) :
    H2Poly (I := I) (M := M) g P n B S := by
  have hX : 0 ≤
      (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ n :=
    pow_nonneg (by
      linarith [covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g P]) n
  exact ⟨le_trans hS.1 hAB,
    hS.2.trans (mul_le_mul_of_nonneg_right hAB hX)⟩

omit [NeZero (Module.finrank ℝ E)] in
private theorem raise1_l2_sq
    (g : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 3) (q : ℕ) :
    ‖iteratedCovGrad (I := I) g 1 2 q
        (cometricRaiseSlot0Field (I := I) (M := M) g 1 W)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g 0 3 q W‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq
    (I := I) (M := M) g 1 W q x

omit [NeZero (Module.finrank ℝ E)] in
private theorem raise1_jet
    (g : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 3) (m : ℕ) :
    covariantJetNormSq (I := I) (M := M) g m
        (cometricRaiseSlot0Field (I := I) (M := M) g 1 W) =
      covariantJetNormSq (I := I) (M := M) g m W := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro q _
  exact raise1_l2_sq (I := I) (M := M) g W q

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem traceHess_eq
    (g g₁ : SmoothRiemannianMetric I M) :
    traceHessianCoeff (I := I) (M := M) g g₁ =
      reindexedPureTrace (I := I) (M := M) g g₁ 2
        traceHessianSlotPerm := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [traceHessianCoeff_toSection, reindexedPureTrace,
    reindexCoeffGen_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [reindexCoeffFibGen_apply, pureTrace_toSection,
    traceHessianFib, ContinuousLinearMap.comp_apply,
    domDomCongrFib_apply]

private theorem lieTrace_h2_rf
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (σ : Equiv.Perm (Fin 4)),
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieTraceCoeff (I := I) (M := M) g g₁ σ) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) := by
  obtain ⟨K, hK, htrace⟩ :=
    trace_h2_rf (I := I) (M := M) 2 g hδ₀0 hδ₀
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ σ
  have h23 := covariantJetNormSq_mono (I := I) (M := M) g
    (by omega : 2 ≤ 3) P
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (deTurckLieTraceCoeff (I := I) (M := M) g g₁ σ) =
      covariantJetNormSq (I := I) (M := M) g 2
        (traceHessianCoeff (I := I) (M := M) g g₁) := by
          unfold covariantJetNormSq
          apply Finset.sum_congr rfl
          intro q _
          exact lieArm1_normSq_iteratedCovGrad_dLTC_eq
            (I := I) (M := M) g g₁ σ q
    _ = covariantJetNormSq (I := I) (M := M) g 2
        (reindexedPureTrace (I := I) (M := M) g g₁ 2
          traceHessianSlotPerm) := by
      rw [traceHess_eq (I := I) (M := M) g g₁]
    _ ≤ K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) :=
      htrace g₁ P hP htie hδ_le hδ0 hδ traceHessianSlotPerm
    _ ≤ K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl h23) hK

private theorem liePiece_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3))
        (Ψ : SmoothCcTensor g 1 2)
        {n m : ℕ} {A B : ℝ},
      H2Poly (I := I) (M := M) g P n A
          (deTurckLieTraceCoeff (I := I) (M := M) g g₁ σ) →
      H2Poly (I := I) (M := M) g P m B Ψ →
      H2Poly (I := I) (M := M) g P (n + m)
        (C * A * ((Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) * B)))
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g g₁ σ ρ Ψ) := by
  obtain ⟨C, hC, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 3 4 2
  refine ⟨C, hC, ?_⟩
  intro g₁ P σ ρ Ψ n m A B hTrace hΨ
  have hSlot := hp_slot2 (I := I) (M := M) g P hΨ
  have hApp :=
    hp_app_of (I := I) (M := M) g P C hC
      (happ
        (deTurckLieTraceCoeff (I := I) (M := M) g g₁ σ)
        (slotExtendIter (I := I) (M := M) g 1 2 2 Ψ))
      hTrace hSlot
  have hReindex :=
    hp_reindex (I := I) (M := M) g P ρ hApp
  simpa only [deTurckLieTraceCoeffPiece, slotExtendIter, Nat.reduceAdd] using hReindex

private def r1o0312 : Equiv.Perm (Fin 4) :=
  ⟨![0, 3, 1, 2], ![0, 2, 3, 1], by decide, by decide⟩

private def r1o0213 : Equiv.Perm (Fin 4) :=
  ⟨![0, 2, 1, 3], ![0, 2, 1, 3], by decide, by decide⟩

private def r1o2301 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

private def r1o1302 : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

private def r1o1203 : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

private def r1i102 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def r1i120 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem permApp_eq_rs
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) :
    ccOperatorFieldComp (I := I) (M := M) g r s s
        (permCoeff (I := I) (M := M) g σ) S =
      rsDomDomCongrSection (I := I) (M := M) g r s σ S := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  rw [operatorFieldComposition_toSection, ContinuousLinearMap.comp_apply,
    rsDomDomCongrSection_toSection]
  change Tensor0SSpace.toModel
      (slotPermCLM (I := I) σ x
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          S.toSection x) D)) =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (S.toSection x)) D)
  rw [slotPermCLM_apply, Tensor0SSpace.toModel_ofModel,
    toModel_rsDomDomCongr_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem linearizedRicciConnectionDifferenceOrderOne_split
    (g g₁ : SmoothRiemannianMetric I M) :
    linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g g₁ =
      -(reindexCoeffGen (I := I) (M := M) g 3 4
          (rsDomDomCongrSection (I := I) (M := M) g 3 4 r1o0312
            (connectionDifferenceContravariantInsertionField (I := I) g g₁)) r1i102
        + reindexCoeffGen (I := I) (M := M) g 3 4
            (rsDomDomCongrSection (I := I) (M := M) g 3 4 r1o0213
              (connectionDifferenceContravariantInsertionField (I := I) g g₁)) r1i120
        + rsDomDomCongrSection (I := I) (M := M) g 3 4 r1o2301
            (connectionDifferenceContravariantInsertionField (I := I) g g₁)
        + reindexCoeffGen (I := I) (M := M) g 3 4
            (rsDomDomCongrSection (I := I) (M := M) g 3 4 r1o1302
              (connectionDifferenceContravariantInsertionField (I := I) g g₁)) r1i102
        + reindexCoeffGen (I := I) (M := M) g 3 4
            (rsDomDomCongrSection (I := I) (M := M) g 3 4 r1o1203
              (connectionDifferenceContravariantInsertionField (I := I) g g₁)) r1i120) := by
  rw [← permApp_eq_rs (I := I) (M := M) g r1o0312,
    ← permApp_eq_rs (I := I) (M := M) g r1o0213,
    ← permApp_eq_rs (I := I) (M := M) g r1o2301,
    ← permApp_eq_rs (I := I) (M := M) g r1o1302,
    ← permApp_eq_rs (I := I) (M := M) g r1o1203]
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

private theorem ricciKer_h2_rf
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      H2Poly (I := I) (M := M) g P 1 K
        (linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g g₁) := by
  obtain ⟨Kc, hKc, hconn⟩ :=
    conn_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  let fr : ℝ := Module.finrank ℝ E
  let Ko : ℝ := fr * (fr * Kc)
  let K : ℝ := 46 * Ko
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hKo : 0 ≤ Ko := mul_nonneg hfr (mul_nonneg hfr hKc)
  have hK : 0 ≤ K := mul_nonneg (by norm_num) hKo
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hc :
      H2Poly (I := I) (M := M) g P 1 Kc
        (connectionDifferenceSection (I := I) g₁ g) := by
    refine ⟨hKc, ?_⟩
    simpa only [pow_one] using
      hconn g₁ P hP htie hδ_le hδ0 hδ
  have ho :
      H2Poly (I := I) (M := M) g P 1 Ko
        (connectionDifferenceContravariantInsertionField (I := I) g g₁) := by
    have hs := hp_slot2 (I := I) (M := M) g P hc
    have hr := hp_reindex (I := I) (M := M) g P
      connectionDifferenceContrInsertionReindexPerm hs
    rw [connectionDifferenceContravariantInsertionField_eq_reindex_slotExtend_two]
    change H2Poly (I := I) (M := M) g P 1 Ko
      (reindexCoeffGen (I := I) (M := M) g 3 (2 + 2)
        (slotExtendIter (I := I) (M := M) g 1 2 2
          (connectionDifferenceSection (I := I) g₁ g))
        connectionDifferenceContrInsertionReindexPerm)
    simpa only [Ko, fr, mul_assoc] using hr
  let O : SmoothCcTensor g 3 4 :=
    connectionDifferenceContravariantInsertionField (I := I) g g₁
  let A0 : SmoothCcTensor g 3 4 :=
    reindexCoeffGen (I := I) (M := M) g 3 4
      (rsDomDomCongrSection (I := I) (M := M) g 3 4 r1o0312 O) r1i102
  let A1 : SmoothCcTensor g 3 4 :=
    reindexCoeffGen (I := I) (M := M) g 3 4
      (rsDomDomCongrSection (I := I) (M := M) g 3 4 r1o0213 O) r1i120
  let A2 : SmoothCcTensor g 3 4 :=
    rsDomDomCongrSection (I := I) (M := M) g 3 4 r1o2301 O
  let A3 : SmoothCcTensor g 3 4 :=
    reindexCoeffGen (I := I) (M := M) g 3 4
      (rsDomDomCongrSection (I := I) (M := M) g 3 4 r1o1302 O) r1i102
  let A4 : SmoothCcTensor g 3 4 :=
    reindexCoeffGen (I := I) (M := M) g 3 4
      (rsDomDomCongrSection (I := I) (M := M) g 3 4 r1o1203 O) r1i120
  have h0 : covariantJetNormSq (I := I) (M := M) g 2 A0 =
      covariantJetNormSq (I := I) (M := M) g 2 O := by
    simp only [A0, reindex_h2, rsperm_h2]
  have h1 : covariantJetNormSq (I := I) (M := M) g 2 A1 =
      covariantJetNormSq (I := I) (M := M) g 2 O := by
    simp only [A1, reindex_h2, rsperm_h2]
  have h2 : covariantJetNormSq (I := I) (M := M) g 2 A2 =
      covariantJetNormSq (I := I) (M := M) g 2 O := by
    simp only [A2, rsperm_h2]
  have h3 : covariantJetNormSq (I := I) (M := M) g 2 A3 =
      covariantJetNormSq (I := I) (M := M) g 2 O := by
    simp only [A3, reindex_h2, rsperm_h2]
  have h4 : covariantJetNormSq (I := I) (M := M) g 2 A4 =
      covariantJetNormSq (I := I) (M := M) g 2 O := by
    simp only [A4, reindex_h2, rsperm_h2]
  have h01raw := covariantJetNormSq_add_le (I := I) (M := M) g 2 A0 A1
  have h01 : covariantJetNormSq (I := I) (M := M) g 2 (A0 + A1) ≤
      4 * covariantJetNormSq (I := I) (M := M) g 2 O := by
    rw [h0, h1] at h01raw
    linarith
  have h012raw := covariantJetNormSq_add_le (I := I) (M := M) g 2 (A0 + A1) A2
  have h012 : covariantJetNormSq (I := I) (M := M) g 2 (A0 + A1 + A2) ≤
      10 * covariantJetNormSq (I := I) (M := M) g 2 O := by
    calc
      _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 2 (A0 + A1) +
          covariantJetNormSq (I := I) (M := M) g 2 A2) := h012raw
      _ ≤ 2 * (4 * covariantJetNormSq (I := I) (M := M) g 2 O +
          covariantJetNormSq (I := I) (M := M) g 2 O) :=
        mul_le_mul_of_nonneg_left
          (add_le_add h01 (le_of_eq h2)) (by norm_num)
      _ = _ := by ring
  have h0123raw := covariantJetNormSq_add_le (I := I) (M := M) g 2
    (A0 + A1 + A2) A3
  have h0123 : covariantJetNormSq (I := I) (M := M) g 2
      (A0 + A1 + A2 + A3) ≤
      22 * covariantJetNormSq (I := I) (M := M) g 2 O := by
    calc
      _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 2 (A0 + A1 + A2) +
          covariantJetNormSq (I := I) (M := M) g 2 A3) := h0123raw
      _ ≤ 2 * (10 * covariantJetNormSq (I := I) (M := M) g 2 O +
          covariantJetNormSq (I := I) (M := M) g 2 O) :=
        mul_le_mul_of_nonneg_left
          (add_le_add h012 (le_of_eq h3)) (by norm_num)
      _ = _ := by ring
  have h01234raw := covariantJetNormSq_add_le (I := I) (M := M) g 2
    (A0 + A1 + A2 + A3) A4
  have h01234 : covariantJetNormSq (I := I) (M := M) g 2
      (A0 + A1 + A2 + A3 + A4) ≤
      46 * covariantJetNormSq (I := I) (M := M) g 2 O := by
    calc
      _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 2
          (A0 + A1 + A2 + A3) +
          covariantJetNormSq (I := I) (M := M) g 2 A4) := h01234raw
      _ ≤ 2 * (22 * covariantJetNormSq (I := I) (M := M) g 2 O +
          covariantJetNormSq (I := I) (M := M) g 2 O) :=
        mul_le_mul_of_nonneg_left
          (add_le_add h0123 (le_of_eq h4)) (by norm_num)
      _ = _ := by ring
  have hneg (S : SmoothCcTensor g 3 4) :
      covariantJetNormSq (I := I) (M := M) g 2 (-S) =
        covariantJetNormSq (I := I) (M := M) g 2 S := by
    rw [show -S = (-1 : ℝ) • S by simp]
    rw [covariantJetNormSq_smul]
    norm_num
  rw [linearizedRicciConnectionDifferenceOrderOne_split (I := I) (M := M) g g₁]
  refine ⟨hK, ?_⟩
  rw [hneg]
  change covariantJetNormSq (I := I) (M := M) g 2
      (A0 + A1 + A2 + A3 + A4) ≤ _
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (A0 + A1 + A2 + A3 + A4) ≤
        46 * covariantJetNormSq (I := I) (M := M) g 2 O := h01234
    _ ≤ 46 * (Ko *
        (1 + covariantJetNormSq (I := I) (M := M) g 3 P)) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [O, pow_one] using ho.2) (by norm_num)
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ 1 := by
      simp only [K, pow_one]
      ring

private theorem ricciOne_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      H2Poly (I := I) (M := M) g P 2 K
        (linearizedRicciConnectionDifferenceOrder1CoeffField
          (I := I) (M := M) g g₁) := by
  obtain ⟨Kt, hKt, htrace⟩ :=
    fourtrace_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Kk, hKk, hker⟩ :=
    ricciKer_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨C, hC, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 3 4 2
  let K : ℝ := C * Kt * Kk
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hC hKt) hKk
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have ht :
      H2Poly (I := I) (M := M) g P 1 Kt
        (ricciCometricFourTraceCastG0 (I := I) g g₁) := by
    refine ⟨hKt, ?_⟩
    have h23 := covariantJetNormSq_mono (I := I) (M := M) g
      (by omega : 2 ≤ 3) P
    simpa only [pow_one] using
      (htrace g₁ P hP htie hδ_le hδ0 hδ).trans
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl h23) hKt)
  have hk := hker g₁ P hP htie hδ_le hδ0 hδ
  have hout :=
    hp_app_of (I := I) (M := M) g P C hC
      (happ
        (ricciCometricFourTraceCastG0 (I := I) g g₁)
        (linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g g₁))
      ht hk
  rw [linearizedRicciConnectionDifferenceOrder1CoeffField_eq_ccOperatorFieldComp
    (I := I) (M := M) g g₁]
  simpa only [K, Nat.reduceAdd] using hout

private theorem lieBackground_h2_rf
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      H2Poly (I := I) (M := M) g P 1 K
        (deTurckLieArmOneBackgroundConnectionDifference (I := I) (M := M) g g₁ g) := by
  obtain ⟨Kc, hKc, hconn⟩ :=
    conn_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  let F : SmoothCcTensor g 1 2 :=
    lieArm1FixCd (I := I) (M := M) g g
  let Kf : ℝ := covariantJetNormSq (I := I) (M := M) g 2 F
  let K : ℝ := 2 * (Kc + Kf)
  have hKf : 0 ≤ Kf := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g F
  have hK : 0 ≤ K := mul_nonneg (by norm_num) (add_nonneg hKc hKf)
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hc :
      H2Poly (I := I) (M := M) g P 1 Kc
        (connectionDifferenceSection (I := I) g₁ g) := by
    refine ⟨hKc, ?_⟩
    simpa only [pow_one] using
      hconn g₁ P hP htie hδ_le hδ0 hδ
  have hf0 :
      H2Poly (I := I) (M := M) g P 0 Kf F := by
    simpa only [Kf] using hp_const (I := I) (M := M) g P F
  have hf := hp_raise (I := I) (M := M) g P
    (by omega : 0 ≤ 1) hf0
  have hout := hp_add (I := I) (M := M) g P hc hf
  rw [lieArm1_connectionDifferenceBackground_decomp (I := I) (M := M) g g₁ g]
  simpa only [K, F] using hout

private theorem liePsi_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      H2Poly (I := I) (M := M) g P 2 K
        (deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g g₁ g) := by
  obtain ⟨Km, hKm, hmcd⟩ :=
    mcd_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Ks, hKs, hsharp⟩ :=
    sharp_h3_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨C, hC, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 1 1 2
  let K : ℝ := C * Km * Ks
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hC hKm) hKs
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hm :
      H2Poly (I := I) (M := M) g P 1 Km
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g g₁ g) := by
    refine ⟨hKm, ?_⟩
    simpa only [pow_one] using
      hmcd g₁ P hP htie hδ_le hδ0 hδ
  rw [metricConnectionDifferenceLoweredCoefficient_eq_neg_kappa
    (I := I) (M := M) g g₁ g] at hm
  have hk0 := hp_smul (I := I) (M := M) g P (-1) hm
  have hk :
      H2Poly (I := I) (M := M) g P 1 Km
        (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g g₁ g) := by
    simpa only [neg_one_sq, one_mul, neg_one_smul, neg_neg] using hk0
  have hp :=
    hp_domperm (I := I) (M := M) g P lieArm1RhoSlot0 hk
  have hr :
      H2Poly (I := I) (M := M) g P 1 Km
        (cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g lieArm1RhoSlot0
            (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g g₁ g))) := by
    refine ⟨hKm, ?_⟩
    rw [raise1_jet (I := I) (M := M)]
    exact hp.2
  have hs :
      H2Poly (I := I) (M := M) g P 1 Ks
        (sharpFlatEndoCc (I := I) g g₁) := by
    refine ⟨hKs, ?_⟩
    simpa only [pow_one] using
      (covariantJetNormSq_mono (I := I) (M := M) g
        (by omega : 2 ≤ 3) (sharpFlatEndoCc (I := I) g g₁)).trans
          (hsharp g₁ P hP htie hδ_le hδ0 hδ)
  have hout :=
    hp_app_of (I := I) (M := M) g P C hC
      (happ
        (cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g lieArm1RhoSlot0
            (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g g₁ g)))
        (sharpFlatEndoCc (I := I) g g₁))
      hr hs
  simpa only [deTurckLieArmOneBackgroundCoefficient, lieArm1RhoSlot0, K, Nat.reduceAdd] using hout

private theorem lieOne_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      H2Poly (I := I) (M := M) g P 3 K
        (deTurckLieArm1Coeff (I := I) (M := M) g g₁ g) := by
  obtain ⟨Kt, hKt, htrace⟩ :=
    lieTrace_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Kc, hKc, hconn⟩ :=
    conn_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Kp, hKp, hpsi⟩ :=
    liePsi_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Kg, hKg, hbg⟩ :=
    lieBackground_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨C, hC, hpiece⟩ :=
    liePiece_h2 (I := I) (M := M) hDim g
  let fr : ℝ := Module.finrank ℝ E
  let Kpc : ℝ := C * Kt * (fr * (fr * Kc))
  let Kpp : ℝ := C * Kt * (fr * (fr * Kp))
  let Kpg : ℝ := C * Kt * (fr * (fr * Kg))
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hKpc : 0 ≤ Kpc :=
    mul_nonneg (mul_nonneg hC hKt)
      (mul_nonneg hfr (mul_nonneg hfr hKc))
  have hKpp : 0 ≤ Kpp :=
    mul_nonneg (mul_nonneg hC hKt)
      (mul_nonneg hfr (mul_nonneg hfr hKp))
  have hKpg : 0 ≤ Kpg :=
    mul_nonneg (mul_nonneg hC hKt)
      (mul_nonneg hfr (mul_nonneg hfr hKg))
  let Q2 : ℝ := 2 * (Kpc + Kpp)
  let Q3 : ℝ := 2 * (Q2 + Kpc)
  let Q4 : ℝ := 2 * (Q3 + Kpc)
  let Q5 : ℝ := 2 * (Q4 + Kpc)
  let Q6 : ℝ := 2 * (Q5 + Kpc)
  let Q7 : ℝ := 2 * (Kpg + Q6)
  let Q8 : ℝ := 2 * (Q7 + Q6)
  let K : ℝ := 2 * (Q8 + Kpc)
  have hQ2 : 0 ≤ Q2 :=
    mul_nonneg (by norm_num) (add_nonneg hKpc hKpp)
  have hQ3 : 0 ≤ Q3 :=
    mul_nonneg (by norm_num) (add_nonneg hQ2 hKpc)
  have hQ4 : 0 ≤ Q4 :=
    mul_nonneg (by norm_num) (add_nonneg hQ3 hKpc)
  have hQ5 : 0 ≤ Q5 :=
    mul_nonneg (by norm_num) (add_nonneg hQ4 hKpc)
  have hQ6 : 0 ≤ Q6 :=
    mul_nonneg (by norm_num) (add_nonneg hQ5 hKpc)
  have hQ7 : 0 ≤ Q7 :=
    mul_nonneg (by norm_num) (add_nonneg hKpg hQ6)
  have hQ8 : 0 ≤ Q8 :=
    mul_nonneg (by norm_num) (add_nonneg hQ7 hQ6)
  have hK : 0 ≤ K :=
    mul_nonneg (by norm_num) (add_nonneg hQ8 hKpc)
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hTrace : ∀ σ : Equiv.Perm (Fin 4),
      H2Poly (I := I) (M := M) g P 1 Kt
        (deTurckLieTraceCoeff (I := I) (M := M) g g₁ σ) := by
    intro σ
    refine ⟨hKt, ?_⟩
    simpa only [pow_one] using
      htrace g₁ P hP htie hδ_le hδ0 hδ σ
  have hConn :
      H2Poly (I := I) (M := M) g P 1 Kc
        (connectionDifferenceSection (I := I) g₁ g) := by
    refine ⟨hKc, ?_⟩
    simpa only [pow_one] using
      hconn g₁ P hP htie hδ_le hδ0 hδ
  have hPsi :=
    hpsi g₁ P hP htie hδ_le hδ0 hδ
  have hBackground :=
    hbg g₁ P hP htie hδ_le hδ0 hδ
  have hPc : ∀ (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      H2Poly (I := I) (M := M) g P 3 Kpc
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g g₁ σ ρ
          (connectionDifferenceSection (I := I) g₁ g)) := by
    intro σ ρ
    have hraw := hpiece g₁ P σ ρ
      (connectionDifferenceSection (I := I) g₁ g) (hTrace σ) hConn
    have hout := hp_raise (I := I) (M := M) g P
      (by omega : 1 + 1 ≤ 3) hraw
    simpa only [Kpc, fr, Nat.reduceAdd] using hout
  have hPp : ∀ (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      H2Poly (I := I) (M := M) g P 3 Kpp
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g g₁ σ ρ
          (deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g g₁ g)) := by
    intro σ ρ
    have hout := hpiece g₁ P σ ρ
      (deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g g₁ g) (hTrace σ) hPsi
    simpa only [Kpp, fr, Nat.reduceAdd] using hout
  have hPg : ∀ (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      H2Poly (I := I) (M := M) g P 3 Kpg
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g g₁ σ ρ
          (deTurckLieArmOneBackgroundConnectionDifference (I := I) (M := M) g g₁ g)) := by
    intro σ ρ
    have hraw := hpiece g₁ P σ ρ
      (deTurckLieArmOneBackgroundConnectionDifference (I := I) (M := M) g g₁ g)
      (hTrace σ) hBackground
    have hout := hp_raise (I := I) (M := M) g P
      (by omega : 1 + 1 ≤ 3) hraw
    simpa only [Kpg, fr, Nat.reduceAdd] using hout
  let Z0 : SmoothCcTensor g 3 2 :=
    deTurckLieTraceCoeffPiece (I := I) (M := M) g g₁ lieArm1SigmaC lieArm1RhoSlot0
      (deTurckLieArmOneBackgroundConnectionDifference (I := I) (M := M) g g₁ g)
  let Z1 : SmoothCcTensor g 3 2 :=
    deTurckLieTraceCoeffPiece (I := I) (M := M) g g₁ lieArm1SigmaA
      (Equiv.refl (Fin 3)) (connectionDifferenceSection (I := I) g₁ g)
  let Z2 : SmoothCcTensor g 3 2 :=
    deTurckLieTraceCoeffPiece (I := I) (M := M) g g₁ lieArm1SigmaA
      (Equiv.refl (Fin 3))
      (deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g g₁ g)
  let Z3 : SmoothCcTensor g 3 2 :=
    deTurckLieTraceCoeffPiece (I := I) (M := M) g g₁ lieArm1SigmaC
      (Equiv.refl (Fin 3)) (connectionDifferenceSection (I := I) g₁ g)
  let Z4 : SmoothCcTensor g 3 2 :=
    deTurckLieTraceCoeffPiece (I := I) (M := M) g g₁ lieArm1SigmaD lieArm1RhoSlot0
      (connectionDifferenceSection (I := I) g₁ g)
  let Z5 : SmoothCcTensor g 3 2 :=
    deTurckLieTraceCoeffPiece (I := I) (M := M) g g₁ (Equiv.refl (Fin 4))
      lieArm1RhoSlot1 (connectionDifferenceSection (I := I) g₁ g)
  let Z6 : SmoothCcTensor g 3 2 :=
    deTurckLieTraceCoeffPiece (I := I) (M := M) g g₁ lieArm1SigmaF
      (Equiv.refl (Fin 3)) (connectionDifferenceSection (I := I) g₁ g)
  let Z7 : SmoothCcTensor g 3 2 :=
    deTurckLieTraceCoeffPiece (I := I) (M := M) g g₁ lieArm1SigmaASwap
      (Equiv.refl (Fin 3)) (connectionDifferenceSection (I := I) g₁ g)
  let Z8 : SmoothCcTensor g 3 2 :=
    deTurckLieTraceCoeffPiece (I := I) (M := M) g g₁ lieArm1SigmaASwap
      (Equiv.refl (Fin 3))
      (deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g g₁ g)
  let Z9 : SmoothCcTensor g 3 2 :=
    deTurckLieTraceCoeffPiece (I := I) (M := M) g g₁ lieArm1SigmaCSwap
      (Equiv.refl (Fin 3)) (connectionDifferenceSection (I := I) g₁ g)
  let Z10 : SmoothCcTensor g 3 2 :=
    deTurckLieTraceCoeffPiece (I := I) (M := M) g g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
      (connectionDifferenceSection (I := I) g₁ g)
  let Z11 : SmoothCcTensor g 3 2 :=
    deTurckLieTraceCoeffPiece (I := I) (M := M) g g₁ lieArm1SigmaESwap lieArm1RhoSlot1
      (connectionDifferenceSection (I := I) g₁ g)
  let Z12 : SmoothCcTensor g 3 2 :=
    deTurckLieTraceCoeffPiece (I := I) (M := M) g g₁ lieArm1SigmaFSwap
      (Equiv.refl (Fin 3)) (connectionDifferenceSection (I := I) g₁ g)
  let Z13 : SmoothCcTensor g 3 2 :=
    deTurckLieTraceCoeffPiece (I := I) (M := M) g g₁ (Equiv.refl (Fin 4))
      lieArm1RhoSlot0 (connectionDifferenceSection (I := I) g₁ g)
  have hZ0 : H2Poly (I := I) (M := M) g P 3 Kpg Z0 :=
    hPg lieArm1SigmaC lieArm1RhoSlot0
  have hZ1 : H2Poly (I := I) (M := M) g P 3 Kpc Z1 :=
    hPc lieArm1SigmaA (Equiv.refl (Fin 3))
  have hZ2 : H2Poly (I := I) (M := M) g P 3 Kpp Z2 :=
    hPp lieArm1SigmaA (Equiv.refl (Fin 3))
  have hZ3 : H2Poly (I := I) (M := M) g P 3 Kpc Z3 :=
    hPc lieArm1SigmaC (Equiv.refl (Fin 3))
  have hZ4 : H2Poly (I := I) (M := M) g P 3 Kpc Z4 :=
    hPc lieArm1SigmaD lieArm1RhoSlot0
  have hZ5 : H2Poly (I := I) (M := M) g P 3 Kpc Z5 :=
    hPc (Equiv.refl (Fin 4)) lieArm1RhoSlot1
  have hZ6 : H2Poly (I := I) (M := M) g P 3 Kpc Z6 :=
    hPc lieArm1SigmaF (Equiv.refl (Fin 3))
  have hZ7 : H2Poly (I := I) (M := M) g P 3 Kpc Z7 :=
    hPc lieArm1SigmaASwap (Equiv.refl (Fin 3))
  have hZ8 : H2Poly (I := I) (M := M) g P 3 Kpp Z8 :=
    hPp lieArm1SigmaASwap (Equiv.refl (Fin 3))
  have hZ9 : H2Poly (I := I) (M := M) g P 3 Kpc Z9 :=
    hPc lieArm1SigmaCSwap (Equiv.refl (Fin 3))
  have hZ10 : H2Poly (I := I) (M := M) g P 3 Kpc Z10 :=
    hPc lieArm1SigmaDSwap lieArm1RhoSlot0
  have hZ11 : H2Poly (I := I) (M := M) g P 3 Kpc Z11 :=
    hPc lieArm1SigmaESwap lieArm1RhoSlot1
  have hZ12 : H2Poly (I := I) (M := M) g P 3 Kpc Z12 :=
    hPc lieArm1SigmaFSwap (Equiv.refl (Fin 3))
  have hZ13 : H2Poly (I := I) (M := M) g P 3 Kpc Z13 :=
    hPc (Equiv.refl (Fin 4)) lieArm1RhoSlot0
  have hB12 := hp_add (I := I) (M := M) g P hZ1 hZ2
  have hB123 := hp_sub (I := I) (M := M) g P
    (by simpa only [Q2] using hB12) hZ3
  have hB1234 := hp_sub (I := I) (M := M) g P
    (by simpa only [Q3] using hB123) hZ4
  have hB12345 := hp_sub (I := I) (M := M) g P
    (by simpa only [Q4] using hB1234) hZ5
  have hBlock1 := hp_sub (I := I) (M := M) g P
    (by simpa only [Q5] using hB12345) hZ6
  have hB78 := hp_add (I := I) (M := M) g P hZ7 hZ8
  have hB789 := hp_sub (I := I) (M := M) g P
    (by simpa only [Q2] using hB78) hZ9
  have hB78910 := hp_sub (I := I) (M := M) g P
    (by simpa only [Q3] using hB789) hZ10
  have hB7891011 := hp_sub (I := I) (M := M) g P
    (by simpa only [Q4] using hB78910) hZ11
  have hBlock2 := hp_sub (I := I) (M := M) g P
    (by simpa only [Q5] using hB7891011) hZ12
  have hOuter1 := hp_add (I := I) (M := M) g P hZ0
    (by simpa only [Q6] using hBlock1)
  have hOuter2 := hp_add (I := I) (M := M) g P
    (by simpa only [Q7] using hOuter1)
    (by simpa only [Q6] using hBlock2)
  have hAll := hp_add (I := I) (M := M) g P
    (by simpa only [Q8] using hOuter2) hZ13
  rw [deTurckLieArm1Coeff_eq_lieArm1Piece_sum
    (I := I) (M := M) g g₁ g]
  change H2Poly (I := I) (M := M) g P 3 K
    (Z0 + (Z1 + Z2 - Z3 - Z4 - Z5 - Z6) +
      (Z7 + Z8 - Z9 - Z10 - Z11 - Z12) + Z13)
  simpa only [K] using hAll

private theorem rhsOne_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {s : ℝ} (_hs : s ∈ Set.Icc (0 : ℝ) 1),
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g T 0 hδ hδZ s) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 3 := by
  obtain ⟨Kr, hKr, hricci⟩ :=
    ricciOne_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Kl, hKl, hlie⟩ :=
    lieOne_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  let Krs : ℝ := (-2 : ℝ) ^ 2 * Kr
  let K : ℝ := 2 * (Krs + Kl)
  have hKrs : 0 ≤ Krs := mul_nonneg (sq_nonneg _) hKr
  have hK : 0 ≤ K := mul_nonneg (by norm_num) (add_nonneg hKrs hKl)
  refine ⟨K, hK, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ s hs
  let P : SmoothCcTensor g 0 2 := s • T
  let gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδ hδZ s
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    rw [← show convexPerturbation (I := I) g T 0 s = P by
      simp only [P, convexPerturbation, smul_zero, zero_add]]
    exact metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hδ hδZ hs_mem x u v
  have hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [P, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδ hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [P, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith only [hs.1, hs.2]
  have hPjet :
      covariantJetNormSq (I := I) (M := M) g 3 P ≤
        covariantJetNormSq (I := I) (M := M) g 3 T := by
    rw [show P = s • T by rfl, covariantJetNormSq_smul]
    exact mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T) hs2
  have hpow (n : ℕ) :
      (1 + covariantJetNormSq (I := I) (M := M) g 3 P) ^ n ≤
        (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ n := by
    exact pow_le_pow_left₀
      (by
        linarith [covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g P])
      (add_le_add le_rfl hPjet) n
  have hRic0 :=
    hricci gm P hP htie hδ_le hδ0 hδP
  have hRic : H2Poly (I := I) (M := M) g T 2 Kr
      (linearizedRicciConnectionDifferenceOrder1CoeffField
        (I := I) (M := M) g gm) := by
    refine ⟨hKr, hRic0.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (hpow 2) hKr
  have hRic3 :=
    hp_raise (I := I) (M := M) g T (by omega : 2 ≤ 3) hRic
  have hRicS :=
    hp_smul (I := I) (M := M) g T (-2 : ℝ) hRic3
  have hLie0 :=
    hlie gm P hP htie hδ_le hδ0 hδP
  have hLie : H2Poly (I := I) (M := M) g T 3 Kl
      (deTurckLieArm1Coeff (I := I) (M := M) g gm g) := by
    refine ⟨hKl, hLie0.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (hpow 3) hKl
  have hout := hp_add (I := I) (M := M) g T hRicS hLie
  simpa only [ricciDeTurckRemainderFirstOrderCoefficient, linearizedRicciConnectionDifferenceOrder1Coeff,
    gm, Krs, K] using hout.2

private theorem oneInt_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M) g g T 0
            (lt_of_le_of_lt hδ_le hδ₀) hδ
            (lt_of_le_of_lt hδ_le hδ₀) hδZ) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 3 := by
  obtain ⟨K, hK, hcoeff⟩ :=
    rhsOne_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  refine ⟨K, hK, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ
  let X : ℝ :=
    K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 3
  have hX : 0 ≤ X := by
    exact mul_nonneg hK (pow_nonneg (by
      linarith [covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T]) 3)
  have hsX : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hpath := path_jetL2_le (I := I) (M := M) g 3 2 2
    (ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g T 0 hδ hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen hSI
    (ricciDeTurckRemainderFirstOrderCoefficient_path_joint (I := I) (M := M) g g T 0 hδ hδZ)
    (fun s hs => by
      rw [hsX]
      simpa only [covariantJetNormSq, X] using
        hcoeff T hT hδ_le hδ0 hδ hδZ hs)
  rw [hsX] at hpath
  simpa only [ricciDeTurckRemainderFirstOrderPathIntegral, covariantJetNormSq, X] using hpath

private theorem lowC1_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (lowerScaleActionCoefficients (I := I) (M := M) g g T
            (lt_of_le_of_lt hδ_le hδ₀) hδ hδZ).firstOrderCoefficient ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 3 := by
  obtain ⟨K, hK, hint⟩ :=
    oneInt_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  refine ⟨K, hK, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ
  simpa only [lowerScaleActionCoefficients] using
    hint T hT hδ_le hδ0 hδ hδZ

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem grad_jet1
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (W : SmoothCcTensor g 0 s) :
    covariantJetNormSq (I := I) (M := M) g 1
        (iteratedCovGrad (I := I) g 0 s 1 W) ≤
      covariantJetNormSq (I := I) (M := M) g 2 W := by
  have h0 := iteratedCovGrad_comp_norm (I := I) (M := M) g s 1 0 W
  have h1 := iteratedCovGrad_comp_norm (I := I) (M := M) g s 1 1 W
  unfold covariantJetNormSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 ⊢
  rw [h0, h1]
  nlinarith only [sq_nonneg ‖W‖]

omit [BoundarylessManifold I M] in
theorem exists_lowerScaleFirstOrderAction_thirdToSecondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : LowerScaleActionCoefficients g) (W : SmoothCcTensor g 0 2)
        (B D : ℝ), 0 ≤ B → 0 ≤ D →
        covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient +
            covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient ≤ B ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 W ≤ D ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2
            (A.firstOrderAction (I := I) (M := M) W) ≤ (C * B * D) ^ 2 := by
  obtain ⟨C0, hC0, happ0⟩ :=
    operatorFieldApplication_h2_h2_h2 (I := I) (M := M) hDim g 2 2
  obtain ⟨C1, hC1, happ1⟩ :=
    operatorFieldApplication_h2_h2_h2 (I := I) (M := M) hDim g 3 2
  let C : ℝ := 2 * (C0 + C1)
  refine ⟨C, mul_nonneg (by norm_num) (add_nonneg hC0 hC1), ?_⟩
  intro A W B D hB hD hA hW
  have hA0 : covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient ≤ B ^ 2 := by
    nlinarith only [hA, covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g A.firstOrderCoefficient]
  have hA1 : covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient ≤ B ^ 2 := by
    nlinarith only [hA, covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g A.zeroOrderCoefficient]
  have hW2 : covariantJetNormSq (I := I) (M := M) g 2 W ≤ D ^ 2 :=
    (covariantJetNormSq_mono (I := I) (M := M) g (by omega : 2 ≤ 3) W).trans hW
  have hGW : covariantJetNormSq (I := I) (M := M) g 2
      (iteratedCovGrad (I := I) g 0 2 1 W) ≤ D ^ 2 :=
    (grad_jet2 (I := I) (M := M) g W).trans hW
  have hY0 : covariantJetNormSq (I := I) (M := M) g 2
      (operatorFieldApply (I := I) (M := M) g 2 2 A.zeroOrderCoefficient W) ≤
        (C0 * B * D) ^ 2 := by
    simpa only [covariantJetNormSq, Nat.reduceAdd] using
      happ0 A.zeroOrderCoefficient W B D hB hD
        (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hA0)
        (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hW2)
  have hY1 : covariantJetNormSq (I := I) (M := M) g 2
      (operatorFieldApply (I := I) (M := M) g 3 2 A.firstOrderCoefficient
        (iteratedCovGrad (I := I) g 0 2 1 W)) ≤
        (C1 * B * D) ^ 2 := by
    simpa only [covariantJetNormSq, Nat.reduceAdd] using
      happ1 A.firstOrderCoefficient (iteratedCovGrad (I := I) g 0 2 1 W)
        B D hB hD
        (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hA1)
        (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hGW)
  have hcoef :
      2 * (C0 ^ 2 + C1 ^ 2) ≤ (2 * (C0 + C1)) ^ 2 := by
    nlinarith only [mul_nonneg hC0 hC1]
  rw [LowerScaleActionCoefficients.firstOrderAction]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2 A.zeroOrderCoefficient W +
          operatorFieldApply (I := I) (M := M) g 3 2 A.firstOrderCoefficient
            (iteratedCovGrad (I := I) g 0 2 1 W)) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2
            (operatorFieldApply (I := I) (M := M) g 2 2 A.zeroOrderCoefficient W) +
          covariantJetNormSq (I := I) (M := M) g 2
            (operatorFieldApply (I := I) (M := M) g 3 2 A.firstOrderCoefficient
              (iteratedCovGrad (I := I) g 0 2 1 W))) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _
    _ ≤ 2 * ((C0 * B * D) ^ 2 + (C1 * B * D) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hY0 hY1) (by norm_num)
    _ = (2 * (C0 ^ 2 + C1 ^ 2)) * (B * D) ^ 2 := by ring
    _ ≤ (2 * (C0 + C1)) ^ 2 * (B * D) ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    _ = (C * B * D) ^ 2 := by simp only [C]; ring

theorem exists_lowerScaleFirstOrderAction_secondToFirstOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : LowerScaleActionCoefficients g) (W : SmoothCcTensor g 0 2)
        (B D : ℝ), 0 ≤ B → 0 ≤ D →
        covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient +
            covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient ≤ B ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ D ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 1
            (A.firstOrderAction (I := I) (M := M) W) ≤ (C * B * D) ^ 2 := by
  obtain ⟨C0, hC0, happ0⟩ :=
    operator_field_composition_h2_h1_to_h1_bound (I := I) (M := M) hDim g 0 2 2
  obtain ⟨C1, hC1, happ1⟩ :=
    operator_field_composition_h2_h1_to_h1_bound (I := I) (M := M) hDim g 0 3 2
  let C : ℝ := 2 * (C0 + C1)
  refine ⟨C, mul_nonneg (by norm_num) (add_nonneg hC0 hC1), ?_⟩
  intro A W B D hB hD hA hW
  have hA0 : covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient ≤ B ^ 2 := by
    nlinarith only [hA, covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g A.firstOrderCoefficient]
  have hA1 : covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient ≤ B ^ 2 := by
    nlinarith only [hA, covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g A.zeroOrderCoefficient]
  have hW1 : covariantJetNormSq (I := I) (M := M) g 1 W ≤ D ^ 2 :=
    (covariantJetNormSq_mono (I := I) (M := M) g (by omega : 1 ≤ 2) W).trans hW
  have hGW : covariantJetNormSq (I := I) (M := M) g 1
      (iteratedCovGrad (I := I) g 0 2 1 W) ≤ D ^ 2 :=
    (grad_jet1 (I := I) (M := M) g W).trans hW
  let Y0 : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2 A.zeroOrderCoefficient W
  let Y1 : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 3 2 A.firstOrderCoefficient
      (iteratedCovGrad (I := I) g 0 2 1 W)
  have hY0norm :
      ‖(⟨Y0⟩ : SmoothCcTensorH1 g 0 2)‖ ≤ C0 * B * D := by
    simpa only [Y0, operatorFieldComposition_zero_eq_operatorFieldApply] using
      happ0 A.zeroOrderCoefficient W B D hB hD
        (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hA0)
        (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hW1)
  have hY1norm :
      ‖(⟨Y1⟩ : SmoothCcTensorH1 g 0 2)‖ ≤ C1 * B * D := by
    simpa only [Y1, operatorFieldComposition_zero_eq_operatorFieldApply] using
      happ1 A.firstOrderCoefficient (iteratedCovGrad (I := I) g 0 2 1 W)
        B D hB hD
        (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hA1)
        (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hGW)
  have hY0 : covariantJetNormSq (I := I) (M := M) g 1 Y0 ≤
      (C0 * B * D) ^ 2 := by
    have hsq := pow_le_pow_left₀
      (norm_nonneg (⟨Y0⟩ : SmoothCcTensorH1 g 0 2)) hY0norm 2
    rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g 0 2 Y0] at hsq
    simpa only [covariantJetNormSq, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, Nat.reduceAdd,
      iteratedCovGrad_zero, iteratedCovGrad_succ] using hsq
  have hY1 : covariantJetNormSq (I := I) (M := M) g 1 Y1 ≤
      (C1 * B * D) ^ 2 := by
    have hsq := pow_le_pow_left₀
      (norm_nonneg (⟨Y1⟩ : SmoothCcTensorH1 g 0 2)) hY1norm 2
    rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g 0 2 Y1] at hsq
    simpa only [covariantJetNormSq, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, Nat.reduceAdd,
      iteratedCovGrad_zero, iteratedCovGrad_succ] using hsq
  have hcoef :
      2 * (C0 ^ 2 + C1 ^ 2) ≤ (2 * (C0 + C1)) ^ 2 := by
    nlinarith only [mul_nonneg hC0 hC1]
  change covariantJetNormSq (I := I) (M := M) g 1 (Y0 + Y1) ≤ _
  calc
    covariantJetNormSq (I := I) (M := M) g 1 (Y0 + Y1) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 1 Y0 +
          covariantJetNormSq (I := I) (M := M) g 1 Y1) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 1 Y0 Y1
    _ ≤ 2 * ((C0 * B * D) ^ 2 + (C1 * B * D) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hY0 hY1) (by norm_num)
    _ = (2 * (C0 ^ 2 + C1 ^ 2)) * (B * D) ^ 2 := by ring
    _ ≤ (2 * (C0 + C1)) ^ 2 * (B * D) ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    _ = (C * B * D) ^ 2 := by simp only [C]; ring

theorem exists_lowerScaleSecondOrderCoefficient_smallPerturbation_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ (1 : ℝ) / 3) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
      let A := lowerScaleActionCoefficients (I := I) (M := M) g g T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ
      (∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            (A.secondOrderCoefficient.toSection x) ≤ (C * R) ^ 2) ∧
        covariantJetNormSq (I := I) (M := M) g 2 A.secondOrderCoefficient ≤ (C * R) ^ 2 := by
  obtain ⟨ρp, Cp, hρp, hCp, hphi⟩ :=
    phi_dev_h2 (I := I) (M := M) hDim g
  obtain ⟨Chs, hChs, hhs⟩ :=
    hs2_low2 (I := I) (M := M) g 2
  obtain ⟨Cl, hCl, hlie⟩ :=
    lieSecondOrderExpansion_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Cr, hCr, hricci⟩ :=
    ricciTop_h2 (I := I) (M := M) hDim g
  obtain ⟨Cpt, hCpt, hpoint⟩ :=
    jet2_fiber (I := I) (M := M) hDim g 4 2
  let ρj : ℝ := 1 / (Chs + 1)
  let ρ : ℝ := min ρp ρj
  let Bl : ℝ := Cl * Chs
  let Br : ℝ := 2 * Cr * Chs
  let Z : ℝ := 4 * Bl ^ 2 + 4 * Cp ^ 2 + 2 * Br ^ 2
  let B : ℝ := Real.sqrt Z
  let C : ℝ := (Cpt + 1) * B
  have hρj : 0 < ρj := by
    dsimp only [ρj]
    positivity
  have hρ : 0 < ρ := by
    exact lt_min hρp hρj
  have hBl : 0 ≤ Bl := mul_nonneg hCl hChs
  have hBr : 0 ≤ Br :=
    mul_nonneg (mul_nonneg (by norm_num) hCr) hChs
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    positivity
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hC : 0 ≤ C :=
    mul_nonneg (by linarith) hB
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ R hR0 hRρ hTHs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hRphi : R ≤ ρp :=
    hRρ.trans (min_le_left ρp ρj)
  have hRj : R ≤ ρj :=
    hRρ.trans (min_le_right ρp ρj)
  let A0 : ℝ := Chs * R
  have hA0 : 0 ≤ A0 := mul_nonneg hChs hR0
  have hA1 : A0 ≤ 1 := by
    have hden : 0 < Chs + 1 := by linarith
    have hfrac : Chs / (Chs + 1) < (1 : ℝ) :=
      (div_lt_one hden).2 (by linarith)
    calc
      A0 ≤ Chs * (1 / (Chs + 1)) :=
        mul_le_mul_of_nonneg_left hRj hChs
      _ = Chs / (Chs + 1) := by ring
      _ ≤ 1 := le_of_lt hfrac
  have hT2 :
      covariantJetNormSq (I := I) (M := M) g 2 T ≤ A0 ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 T ≤
          (Chs *
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) ^ 2 := by
        simpa only [covariantJetNormSq, Nat.reduceAdd] using hhs T
      _ ≤ (Chs * R) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hChs (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hTHs hChs) 2
      _ = A0 ^ 2 := by rfl
  let Φ : ℝ → SmoothCcTensor g 4 2 :=
    rhsDecompositionTop (I := I) (M := M) g T hδ hδZ
  let Ψ : ℝ → SmoothCcTensor g 4 2 :=
    ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ
  let K : SmoothCcTensor g 4 2 :=
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hjΦ := rhsDecompositionTop_joint (I := I) (M := M)
    g T hδ_lt hδ hδZ
  have hjΨ := selfTop_joint (I := I) (M := M) g T hδ hδZ
  have hjK := arm_const (I := I) (M := M) g
    (δ := δ) (δ' := δ) K
  have hjAll := threeArmJoint_sub (I := I) (M := M) g _ _
    (threeArmJoint_add (I := I) (M := M) g _ _ hjΦ hjΨ) hjK
  have hzeroHs :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (0 : SmoothCcTensor g 0 2)‖ ≤ R := by
    have hz :
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (0 : SmoothCcTensor g 0 2) = 0 := by
      rw [show (0 : SmoothCcTensor g 0 2) =
          (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
        ccTensorToHs_smul, zero_smul]
    rw [hz, norm_zero]
    exact hR0
  have hkernel : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      covariantJetNormSq (I := I) (M := M) g 2 (Φ s + Ψ s - K) ≤
        (B * R) ^ 2 := by
    intro s hs
    let P : SmoothCcTensor g 0 2 :=
      convexPerturbation (I := I) g T 0 s
    let gm : SmoothRiemannianMetric I M :=
      metricPerturbationPath (I := I) g T 0 hδ hδZ s
    have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
      Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
    have htie : ∀ (x : M) (u v : TangentSpace I x),
        gm.inner x u v =
          g.inner x u v + ccTensorBilinSymm (I := I) g P x u v :=
      fun x u v => metricPerturbationPath_inner_of_mem
        (I := I) g T 0 hδ hδZ hs_mem x u v
    have hδP : gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g P) δ := by
      convert convexPerturbation_gFibreOpBound
        (I := I) (M := M) g T 0 hδ hδZ hs.1 hs.2 using 1
      all_goals ring
    have hcP : P = s • T := by
      simp only [P, convexPerturbation, smul_zero, zero_add]
    have hP : ∀ (x : M) (u v : TangentSpace I x),
        ccTensorBilin (I := I) g P x u v =
          ccTensorBilin (I := I) g P x v u := by
      intro x u v
      rw [hcP]
      simp only [ccTensorBilin_apply, ccTensorModel_smul,
        smul_apply, smul_eq_mul]
      apply congrArg (fun z : ℝ => s * z)
      simpa only [ccTensorBilin_apply] using hT x u v
    have hs2 : s ^ 2 ≤ (1 : ℝ) := by
      nlinarith only [hs.1, hs.2]
    have hP2 :
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ 1 := by
      rw [hcP, covariantJetNormSq_smul]
      calc
        s ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 T ≤
            covariantJetNormSq (I := I) (M := M) g 2 T :=
          mul_le_of_le_one_left
            (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T) hs2
        _ ≤ A0 ^ 2 := hT2
        _ ≤ 1 := by nlinarith only [hA0, hA1]
    have hL0 :=
      hlie T hT hδ_le hδ0 hδ hδZ A0 hA0 hA1 hT2 hs
    have hL :
        covariantJetNormSq (I := I) (M := M) g 2
            (lieDecomposition2 (I := I) (M := M) g T hδ hδZ s) ≤
          (Bl * R) ^ 2 := by
      simpa only [Bl, A0, mul_assoc] using hL0
    have hP0 :=
      hphi T (0 : SmoothCcTensor g 0 2)
        hδ_lt hδ hδ_lt hδZ hR0 hRphi hTHs hzeroHs hs.1 hs.2
    have hPhi :
        covariantJetNormSq (I := I) (M := M) g 2
            (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gm -
              deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g) ≤
          (Cp * R) ^ 2 := by
      simpa only [covariantJetNormSq, Nat.reduceAdd, gm] using hP0.2
    have hRic0 :=
      hricci gm P T hP htie hδ_le hδ0 hδP
        A0 hA0 hP2 hT2
    have hRic :
        covariantJetNormSq (I := I) (M := M) g 2
            ((-2 * s : ℝ) •
              ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T) ≤
          (Br * R) ^ 2 := by
      rw [covariantJetNormSq_smul]
      calc
        (-2 * s) ^ 2 *
            covariantJetNormSq (I := I) (M := M) g 2
              (ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T) ≤
          4 * covariantJetNormSq (I := I) (M := M) g 2
              (ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T) :=
          mul_le_mul_of_nonneg_right
            (by nlinarith only [hs.1, hs.2])
            (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
        _ ≤ 4 * (Cr * A0) ^ 2 :=
          mul_le_mul_of_nonneg_left hRic0 (by norm_num)
        _ = (Br * R) ^ 2 := by
          simp only [Br, A0]
          ring
    rw [show Φ s + Ψ s - K =
        lieDecomposition2 (I := I) (M := M) g T hδ hδZ s +
          (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gm -
            deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g) +
          (-2 * s : ℝ) •
            ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T by
      simpa only [Φ, Ψ, K, gm] using
        topKernel_eq (I := I) (M := M) g T hδ hδZ s]
    have hLP :
        covariantJetNormSq (I := I) (M := M) g 2
            (lieDecomposition2 (I := I) (M := M) g T hδ hδZ s +
              (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gm -
                deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g)) ≤
          2 * ((Bl * R) ^ 2 + (Cp * R) ^ 2) := by
      exact (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans
        (mul_le_mul_of_nonneg_left
          (add_le_add hL hPhi) (by norm_num))
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (lieDecomposition2 (I := I) (M := M) g T hδ hδZ s +
            (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gm -
              deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g) +
            (-2 * s : ℝ) •
              ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2
              (lieDecomposition2 (I := I) (M := M) g T hδ hδZ s +
                (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gm -
                  deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g)) +
          covariantJetNormSq (I := I) (M := M) g 2
              ((-2 * s : ℝ) •
                ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T)) :=
          covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _
      _ ≤ 2 * (2 * ((Bl * R) ^ 2 + (Cp * R) ^ 2) +
          (Br * R) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hLP hRic) (by norm_num)
      _ = Z * R ^ 2 := by
        simp only [Z]
        ring
      _ = (B * R) ^ 2 := by
        rw [mul_pow, show B ^ 2 = Z by
          simpa only [B] using Real.sq_sqrt hZ]
  have hJetRaw :
      covariantJetNormSq (I := I) (M := M) g 2
          (rhsDecompositionTopInt (I := I) (M := M) g T
              hδ_lt hδ hδZ +
            selfTopInt (I := I) (M := M) g T hδ_lt hδ hδZ -
            deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g) ≤
        (B * R) ^ 2 := by
    apply path_add_sub_h2 (I := I) (M := M) g 4
      hSI Φ Ψ K hjΦ hjΨ hjAll (B * R)
    exact hkernel
  let A : LowerScaleActionCoefficients g :=
    lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδ hδZ
  have hJetA :
      covariantJetNormSq (I := I) (M := M) g 2 A.secondOrderCoefficient ≤
        (B * R) ^ 2 := by
    simpa only [A, lowerScaleActionCoefficients] using hJetRaw
  have hBC : B ≤ C := by
    dsimp only [C]
    nlinarith only [mul_nonneg hCpt hB]
  have hBCR : B * R ≤ C * R :=
    mul_le_mul_of_nonneg_right hBC hR0
  have hJetC :
      covariantJetNormSq (I := I) (M := M) g 2 A.secondOrderCoefficient ≤
        (C * R) ^ 2 :=
    hJetA.trans
      (pow_le_pow_left₀ (mul_nonneg hB hR0) hBCR 2)
  change
    (∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          (A.secondOrderCoefficient.toSection x) ≤ (C * R) ^ 2) ∧
      covariantJetNormSq (I := I) (M := M) g 2 A.secondOrderCoefficient ≤ (C * R) ^ 2
  refine ⟨?_, hJetC⟩
  intro x
  have hpt := hpoint A.secondOrderCoefficient x
  have hptfac : Cpt * B ≤ C := by
    dsimp only [C]
    nlinarith only [hB]
  have hptfac0 : 0 ≤ Cpt * B := mul_nonneg hCpt hB
  calc
    riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        (A.secondOrderCoefficient.toSection x) ≤
      Cpt ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 A.secondOrderCoefficient := hpt
    _ ≤ Cpt ^ 2 * (B * R) ^ 2 :=
      mul_le_mul_of_nonneg_left hJetA (sq_nonneg Cpt)
    _ = (Cpt * B * R) ^ 2 := by ring
    _ ≤ (C * R) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hptfac0 hR0)
        (mul_le_mul_of_nonneg_right hptfac hR0) 2

theorem exists_ricciDeTurckRemainder_diagonal_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ κ : ℝ, ∃ D : ℝ → ℝ,
      0 ≤ κ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      let L : LowerScaleActionCoefficients g :=
        lowerScaleActionCoefficients (I := I) (M := M) g g T
          (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ
      deTurckSmoothRemainder (I := I) g g T
            (lt_of_le_of_lt hδ_le (by norm_num)) hδ -
          deTurckSmoothRemainder (I := I) g g
            (0 : SmoothCcTensor g 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num)) hδZ =
        L.secondOrderAction (I := I) (M := M) T + L.firstOrderAction (I := I) (M := M) T ∧
      (∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            (L.secondOrderCoefficient.toSection x) ≤
          (κ * (δ / (1 - δ) ^ 2)) ^ 2) ∧
      covariantJetNormSq (I := I) (M := M) g 2
          (L.firstOrderAction (I := I) (M := M) T) ≤
        (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨κ, hκ, hsplit⟩ :=
    lowData_split (I := I) (M := M) g g
  obtain ⟨D, hD, hdiag⟩ :=
    lowA1_act_tame (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  refine ⟨κ, D, hκ, hD, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let L : LowerScaleActionCoefficients g :=
    lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδ hδZ
  have hs := hsplit T hT hδ_le hδ0 hδ hδZ
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simpa only [L] using hs.1
  · simpa only [L] using hs.2
  · simpa only [L] using
      hdiag T hT hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3

theorem exists_lowerScaleAction_coefficient_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
      let A : LowerScaleActionCoefficients g :=
        lowerScaleActionCoefficients (I := I) (M := M) g g T
          (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ
      covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient +
          covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 6 := by
  obtain ⟨K0, hK0, hC0⟩ :=
    lowC0_h2_rf (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨K1, hK1, hC1⟩ :=
    lowC1_h2_rf (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let K : ℝ := K0 + K1
  have hK : 0 ≤ K := add_nonneg hK0 hK1
  refine ⟨K, hK, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ
  dsimp only
  let A : LowerScaleActionCoefficients g :=
    lowerScaleActionCoefficients (I := I) (M := M) g g T
      (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ
  let X : ℝ := 1 + covariantJetNormSq (I := I) (M := M) g 3 T
  have hX1 : 1 ≤ X := by
    simp only [X]
    linarith [covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T]
  have hX36 : X ^ 3 ≤ X ^ 6 :=
    pow_le_pow_right₀ hX1 (by omega)
  have hA0 :
      covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient ≤ K0 * X ^ 6 := by
    simpa only [A, X] using
      hC0 T hT hδ_le hδ0 hδ hδZ
  have hA1 :
      covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient ≤ K1 * X ^ 3 := by
    simpa only [A, X] using
      hC1 T hT hδ_le hδ0 hδ hδZ
  change
    covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient +
        covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient ≤ K * X ^ 6
  calc
    covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient +
        covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient ≤
      K0 * X ^ 6 + K1 * X ^ 3 := add_le_add hA0 hA1
    _ ≤ K0 * X ^ 6 + K1 * X ^ 6 :=
      add_le_add_right (mul_le_mul_of_nonneg_left hX36 hK1) _
    _ = K * X ^ 6 := by simp only [K]; ring

theorem ricciDeTurckRemainder_lowOrder_split
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ κ K : ℝ, 0 ≤ κ ∧ 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
      ∃ A : LowerScaleActionCoefficients g,
        deTurckSmoothRemainder (I := I) g g T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδ -
            deTurckSmoothRemainder (I := I) g g
              (0 : SmoothCcTensor g 0 2)
              (lt_of_le_of_lt hδ_le (by norm_num)) hδZ =
          A.secondOrderAction (I := I) (M := M) T + A.firstOrderAction (I := I) (M := M) T ∧
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              (A.secondOrderCoefficient.toSection x) ≤
            (κ * (δ / (1 - δ) ^ 2)) ^ 2) ∧
        (∀ W : SmoothCcTensor g 0 2,
          covariantJetNormSq (I := I) (M := M) g 2
              (A.firstOrderAction (I := I) (M := M) W) ≤
            K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 6 *
              covariantJetNormSq (I := I) (M := M) g 3 W) ∧
        ∀ W : SmoothCcTensor g 0 2,
          covariantJetNormSq (I := I) (M := M) g 1
              (A.firstOrderAction (I := I) (M := M) W) ≤
            K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 6 *
              covariantJetNormSq (I := I) (M := M) g 2 W := by
  obtain ⟨κ, hκ, hsplit⟩ :=
    lowData_split (I := I) (M := M) g g
  obtain ⟨K0, hK0, hC0⟩ :=
    lowC0_h2_rf (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨K1, hK1, hC1⟩ :=
    lowC1_h2_rf (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨C3, hC3, hA3⟩ :=
    exists_lowerScaleFirstOrderAction_thirdToSecondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨C2, hC2, hA2⟩ :=
    exists_lowerScaleFirstOrderAction_secondToFirstOrder_bound (I := I) (M := M) hDim g
  let Kc : ℝ := K0 + K1
  let K : ℝ := (C3 ^ 2 + C2 ^ 2) * Kc
  have hKc : 0 ≤ Kc := by
    simpa only [Kc] using add_nonneg hK0 hK1
  have hK : 0 ≤ K := by
    exact mul_nonneg (add_nonneg (sq_nonneg C3) (sq_nonneg C2)) hKc
  refine ⟨κ, K, hκ, hK, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let A : LowerScaleActionCoefficients g :=
    lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδ hδZ
  let X : ℝ := 1 + covariantJetNormSq (I := I) (M := M) g 3 T
  have hX0 : 0 ≤ X := by
    simp only [X]
    linarith [covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T]
  have hX1 : 1 ≤ X := by
    simp only [X]
    linarith [covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T]
  have hX36 : X ^ 3 ≤ X ^ 6 :=
    pow_le_pow_right₀ hX1 (by omega)
  have hA0 :
      covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient ≤ K0 * X ^ 6 := by
    simpa only [A, X] using
      hC0 T hT hδ_le hδ0 hδ hδZ
  have hA1 :
      covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient ≤ K1 * X ^ 3 := by
    simpa only [A, X] using
      hC1 T hT hδ_le hδ0 hδ hδZ
  have hcoeff :
      covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient +
          covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient ≤ Kc * X ^ 6 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient +
          covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient ≤
          K0 * X ^ 6 + K1 * X ^ 3 :=
        add_le_add hA0 hA1
      _ ≤ K0 * X ^ 6 + K1 * X ^ 6 :=
        add_le_add_right (mul_le_mul_of_nonneg_left hX36 hK1) _
      _ = Kc * X ^ 6 := by simp only [Kc]; ring
  have hsplitA := hsplit T hT hδ_le hδ0 hδ hδZ
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · simpa only [A] using hsplitA.1
  · simpa only [A] using hsplitA.2
  · intro W
    let JW : ℝ := covariantJetNormSq (I := I) (M := M) g 3 W
    let B : ℝ := Real.sqrt (Kc * X ^ 6)
    let D : ℝ := Real.sqrt JW
    have hQ : 0 ≤ Kc * X ^ 6 :=
      mul_nonneg hKc (pow_nonneg hX0 6)
    have hJW : 0 ≤ JW := by
      simpa only [JW] using
        covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g W
    have hB : 0 ≤ B := Real.sqrt_nonneg _
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hBsq : B ^ 2 = Kc * X ^ 6 := by
      simpa only [B] using Real.sq_sqrt hQ
    have hDsq : D ^ 2 = JW := by
      simpa only [D] using Real.sq_sqrt hJW
    have hraw := hA3 A W B D hB hD
      (by simpa only [hBsq] using hcoeff)
      (by rw [hDsq])
    have hC :
        C3 ^ 2 * Kc ≤ (C3 ^ 2 + C2 ^ 2) * Kc :=
      mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (sq_nonneg C2)) hKc
    have htail : 0 ≤ X ^ 6 * JW :=
      mul_nonneg (pow_nonneg hX0 6) hJW
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (A.firstOrderAction (I := I) (M := M) W) ≤ (C3 * B * D) ^ 2 := hraw
      _ = (C3 ^ 2 * Kc) * (X ^ 6 * JW) := by
        rw [show (C3 * B * D) ^ 2 = C3 ^ 2 * B ^ 2 * D ^ 2 by ring,
          hBsq, hDsq]
        ring
      _ ≤ ((C3 ^ 2 + C2 ^ 2) * Kc) * (X ^ 6 * JW) :=
        mul_le_mul_of_nonneg_right hC htail
      _ = K * X ^ 6 * JW := by simp only [K]; ring
      _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 6 *
          covariantJetNormSq (I := I) (M := M) g 3 W := by
        simp only [X, JW]
  · intro W
    let JW : ℝ := covariantJetNormSq (I := I) (M := M) g 2 W
    let B : ℝ := Real.sqrt (Kc * X ^ 6)
    let D : ℝ := Real.sqrt JW
    have hQ : 0 ≤ Kc * X ^ 6 :=
      mul_nonneg hKc (pow_nonneg hX0 6)
    have hJW : 0 ≤ JW := by
      simpa only [JW] using
        covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g W
    have hB : 0 ≤ B := Real.sqrt_nonneg _
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hBsq : B ^ 2 = Kc * X ^ 6 := by
      simpa only [B] using Real.sq_sqrt hQ
    have hDsq : D ^ 2 = JW := by
      simpa only [D] using Real.sq_sqrt hJW
    have hraw := hA2 A W B D hB hD
      (by simpa only [hBsq] using hcoeff)
      (by rw [hDsq])
    have hC :
        C2 ^ 2 * Kc ≤ (C3 ^ 2 + C2 ^ 2) * Kc :=
      mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (sq_nonneg C3)) hKc
    have htail : 0 ≤ X ^ 6 * JW :=
      mul_nonneg (pow_nonneg hX0 6) hJW
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (A.firstOrderAction (I := I) (M := M) W) ≤ (C2 * B * D) ^ 2 := hraw
      _ = (C2 ^ 2 * Kc) * (X ^ 6 * JW) := by
        rw [show (C2 * B * D) ^ 2 = C2 ^ 2 * B ^ 2 * D ^ 2 by ring,
          hBsq, hDsq]
        ring
      _ ≤ ((C3 ^ 2 + C2 ^ 2) * Kc) * (X ^ 6 * JW) :=
        mul_le_mul_of_nonneg_right hC htail
      _ = K * X ^ 6 * JW := by simp only [K]; ring
      _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 6 *
          covariantJetNormSq (I := I) (M := M) g 2 W := by
        simp only [X, JW]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
