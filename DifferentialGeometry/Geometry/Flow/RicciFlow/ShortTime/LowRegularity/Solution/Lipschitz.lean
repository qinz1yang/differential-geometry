import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Remainder.PrincipalResidual
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Coefficients.FirstOrderLipschitzBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Action.LowerScaleSobolevExtensions
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Naturality
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.InteriorProductJetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrection.ZeroOrder.ReindexedPureTraceCovariantJet
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.SlotIdentities

noncomputable section


open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance (x : M) :
    ContinuousAdd (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ContinuousLinearMap.topologicalAddGroup.toContinuousAdd

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
private theorem app_sub_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W V : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s Φ (W - V) =
      operatorFieldApply (I := I) (M := M) g r s Φ W -
        operatorFieldApply (I := I) (M := M) g r s Φ V := by
  rw [sub_eq_add_neg, operatorFieldApplication_add_right]
  have hneg := operatorFieldApplication_smul_right (I := I) (M := M) g r s
    (-1 : ℝ) Φ V
  simp only [neg_one_smul] at hneg
  rw [hneg]
  rfl

noncomputable def lowerScaleDiff
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    LowerScaleActionCoefficients g :=
  (lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδT hδZ).firstOrderCoefficientDifference
    (lowerScaleActionCoefficients (I := I) (M := M) g g U hδ_lt hδU hδZ)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem rhsLow1_sub
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g T 0 hδT hδZ s -
        ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g U 0 hδU hδZ s =
      (-2 : ℝ) •
          (linearizedRicciConnectionDifferenceOrder1Coeff
              (I := I) g T 0 hδT hδZ s -
            linearizedRicciConnectionDifferenceOrder1Coeff
              (I := I) g U 0 hδU hδZ s) +
        (deTurckLieFirstOrderCoeff (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g -
          deTurckLieFirstOrderCoeff (I := I) (M := M) g
            (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g) := by
  simp only [ricciDeTurckRemainderFirstOrderCoefficient, smul_sub]
  abel

noncomputable def firstOrderCoefficientDifference
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 3 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 3 2
    (fun s =>
      ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g T 0 hδT hδZ s -
        ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g U 0 hδU hδZ s)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (covariantJetJoint_sub (I := I) (M := M) g _ _
      (ricciDeTurckRemainderFirstOrderCoefficient_path_joint (I := I) (M := M) g g T 0 hδT hδZ)
      (ricciDeTurckRemainderFirstOrderCoefficient_path_joint (I := I) (M := M) g g U 0 hδU hδZ))

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem firstOrderCoefficientDifference_toModel
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) (x : M) :
    TensorRSSpace.toModel
        ((firstOrderCoefficientDifference (I := I) (M := M)
          g T U hδ_lt hδT hδU hδZ).toSection x) =
      ∫ s in (0 : ℝ)..1, TensorRSSpace.toModel
        ((ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M)
            g g T 0 hδT hδZ s -
          ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M)
            g g U 0 hδU hδZ s).toSection x) := by
  unfold firstOrderCoefficientDifference
  exact pathIntegralCoeffField_toModel (I := I) (M := M) g 3 2 _ _ _ _ _ x

theorem lowerScaleActionCoefficients_firstOrderCoefficient_sub
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    (lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδT hδZ).firstOrderCoefficient -
        (lowerScaleActionCoefficients (I := I) (M := M) g g U hδ_lt hδU hδZ).firstOrderCoefficient =
      firstOrderCoefficientDifference (I := I) (M := M) g T U hδ_lt hδT hδU hδZ := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply TensorRSSpace.toModel_injective
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hTcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 3 2
      (fun s => ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g
        T 0 hδT hδZ s)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (ricciDeTurckRemainderFirstOrderCoefficient_path_joint (I := I) (M := M) g g T 0 hδT hδZ) x
  have hUcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 3 2
      (fun s => ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g
        U 0 hδU hδZ s)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (ricciDeTurckRemainderFirstOrderCoefficient_path_joint (I := I) (M := M) g g U 0 hδU hδZ) x
  have hTint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g
          T 0 hδT hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hTcont.mono hSI).intervalIntegrable
  have hUint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g
          U 0 hδU hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hUcont.mono hSI).intervalIntegrable
  simp only [lowerScaleActionCoefficients, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply, TensorRSSpace.toModel_sub]
  rw [ricciDeTurckRemainderFirstOrderPathIntegral_toModel,
    ricciDeTurckRemainderFirstOrderPathIntegral_toModel,
    firstOrderCoefficientDifference_toModel]
  simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    TensorRSSpace.toModel_sub]
  rw [intervalIntegral.integral_sub hTint hUint]

noncomputable def ricciDeTurckLowOrderDifference
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 2 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 2 2
    (fun s =>
      RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
          g g T hδT hδZ s -
        RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
          g g U hδU hδZ s)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (covariantJetJoint_sub (I := I) (M := M) g _ _
      (RicciDeTurckLowOrder.selfLow_joint
        (I := I) (M := M) g g T hδT hδZ)
      (RicciDeTurckLowOrder.selfLow_joint
        (I := I) (M := M) g g U hδU hδZ))

omit [SigmaCompactSpace M] in
theorem ricciDeTurckLowOrderDifference_toModel
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) (x : M) :
    TensorRSSpace.toModel
        ((ricciDeTurckLowOrderDifference (I := I) (M := M)
          g T U hδ_lt hδT hδU hδZ).toSection x) =
      ∫ s in (0 : ℝ)..1, TensorRSSpace.toModel
        ((RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
            g g T hδT hδZ s -
          RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
            g g U hδU hδZ s).toSection x) := by
  unfold ricciDeTurckLowOrderDifference
  exact pathIntegralCoeffField_toModel (I := I) (M := M) g 2 2 _ _ _ _ _ x

omit [SigmaCompactSpace M] in
private theorem selfLow_parts
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
    RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
        g g T hδ hδZ s =
      let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
      ((((-2 : ℝ) •
            RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient
              (I := I) (M := M) g gm (s • T) +
          (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gm g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
              lieDecompositionQ lieDecompositionEps s)) +
        lieCorrectionZeroVectorBundle (I := I) (M := M) g gm) +
        lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g) +
        lieCorrectionZeroRiemann (I := I) (M := M) g gm := by
  rw [RicciDeTurckLowOrder.selfLow_good
    (I := I) (M := M) g g T hT hδ_lt hδ hδZ hs]
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  let Q := deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
    lieDecompositionQ lieDecompositionEps s
  have hlie :
      deTurckLieCoeffField (I := I) (M := M) g gm g +
            lieCorrectionZeroField (I := I) (M := M) g gm g - Q =
        (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gm g - Q) +
          (deTurckLieEndoTermField (I := I) (M := M) g gm g -
            deTurckLieEndoTermField (I := I) (M := M) g gm g) +
          ((((lieCorrectionZeroInsertion (I := I) (M := M) g gm g -
                lieCorrectionZeroInsertion (I := I) (M := M) g gm g) +
              lieCorrectionZeroVectorBundle (I := I) (M := M) g gm) +
            lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g) +
          lieCorrectionZeroRiemann (I := I) (M := M) g gm) := by
    rw [deTurckLieCoeffField_eq_covDerivTerm_add_endoTerm]
    rw [← tail_base_split (I := I) (M := M) g gm g]
    abel
  calc
    _ = (-2 : ℝ) •
          RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient
            (I := I) (M := M) g gm (s • T) +
        (deTurckLieCoeffField (I := I) (M := M) g gm g +
          lieCorrectionZeroField (I := I) (M := M) g gm g - Q) := by
      simp only [gm, Q]
      abel
    _ = (-2 : ℝ) •
          RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient
            (I := I) (M := M) g gm (s • T) +
        ((deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gm g - Q) +
          (deTurckLieEndoTermField (I := I) (M := M) g gm g -
            deTurckLieEndoTermField (I := I) (M := M) g gm g) +
          ((((lieCorrectionZeroInsertion (I := I) (M := M) g gm g -
                lieCorrectionZeroInsertion (I := I) (M := M) g gm g) +
              lieCorrectionZeroVectorBundle (I := I) (M := M) g gm) +
            lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g) +
          lieCorrectionZeroRiemann (I := I) (M := M) g gm)) := by
      rw [hlie]
    _ = _ := by
      simp only [sub_self, zero_add, add_zero]
      abel

theorem lowerScaleActionCoefficients_zeroOrderCoefficient_sub
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    (lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδT hδZ).zeroOrderCoefficient -
        (lowerScaleActionCoefficients (I := I) (M := M) g g U hδ_lt hδU hδZ).zeroOrderCoefficient =
      ricciDeTurckLowOrderDifference (I := I) (M := M) g T U hδ_lt hδT hδU hδZ := by
  classical
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hTcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2
      (RicciDeTurckLowOrder.pathIntegrand
        (I := I) (M := M) g g T hδT hδZ)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (RicciDeTurckLowOrder.selfLow_joint
        (I := I) (M := M) g g T hδT hδZ)
  have hUcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2
      (RicciDeTurckLowOrder.pathIntegrand
        (I := I) (M := M) g g U hδU hδZ)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (RicciDeTurckLowOrder.selfLow_joint
        (I := I) (M := M) g g U hδU hδZ)
  have hInt :
      RicciDeTurckLowOrder.selfLowInt (I := I) (M := M)
            g g T hδ_lt hδT hδZ -
          RicciDeTurckLowOrder.selfLowInt (I := I) (M := M)
            g g U hδ_lt hδU hδZ =
        ricciDeTurckLowOrderDifference (I := I) (M := M)
          g T U hδ_lt hδT hδU hδZ := by
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    apply TensorRSSpace.toModel_injective
    have hTint : IntervalIntegrable
        (fun s : ℝ => TensorRSSpace.toModel
          ((RicciDeTurckLowOrder.pathIntegrand
            (I := I) (M := M) g g T hδT hδZ s).toSection x))
        MeasureTheory.volume 0 1 :=
      ((hTcont x).mono hSI).intervalIntegrable
    have hUint : IntervalIntegrable
        (fun s : ℝ => TensorRSSpace.toModel
          ((RicciDeTurckLowOrder.pathIntegrand
            (I := I) (M := M) g g U hδU hδZ s).toSection x))
        MeasureTheory.volume 0 1 :=
      ((hUcont x).mono hSI).intervalIntegrable
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
    refine (TensorRSSpace.toModel_sub _ _).trans ?_
    rw [RicciDeTurckLowOrder.selfLowInt_toModel,
      RicciDeTurckLowOrder.selfLowInt_toModel]
    rw [← intervalIntegral.integral_sub hTint hUint]
    exact (ricciDeTurckLowOrderDifference_toModel (I := I) (M := M)
      g T U hδ_lt hδT hδU hδZ x).symm
  rw [RicciDeTurckLowOrder.zeroOrderCoefficient_eq, RicciDeTurckLowOrder.zeroOrderCoefficient_eq]
  calc
    (RicciDeTurckLowOrder.selfLowInt (I := I) (M := M)
          g g T hδ_lt hδT hδZ +
        metricPrincipalDefectCurvCoeff (I := I) g g) -
        (RicciDeTurckLowOrder.selfLowInt (I := I) (M := M)
          g g U hδ_lt hδU hδZ +
        metricPrincipalDefectCurvCoeff (I := I) g g) =
      RicciDeTurckLowOrder.selfLowInt (I := I) (M := M)
          g g T hδ_lt hδT hδZ -
        RicciDeTurckLowOrder.selfLowInt (I := I) (M := M)
          g g U hδ_lt hδU hδZ := by
      abel
    _ = ricciDeTurckLowOrderDifference (I := I) (M := M)
        g T U hδ_lt hδT hδU hδZ := hInt

theorem lowerScaleDifference_firstOrderCoefficient
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    (lowerScaleDiff (I := I) (M := M) g T U
        hδ_lt hδT hδU hδZ).firstOrderCoefficient =
      firstOrderCoefficientDifference (I := I) (M := M) g T U
        hδ_lt hδT hδU hδZ := by
  simpa only [lowerScaleDiff, LowerScaleActionCoefficients.firstOrderCoefficientDifference] using
    lowerScaleActionCoefficients_firstOrderCoefficient_sub (I := I) (M := M) g T U hδ_lt hδT hδU hδZ

theorem lowerScaleDifference_zeroOrderCoefficient
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    (lowerScaleDiff (I := I) (M := M) g T U
        hδ_lt hδT hδU hδZ).zeroOrderCoefficient =
      ricciDeTurckLowOrderDifference (I := I) (M := M) g T U
        hδ_lt hδT hδU hδZ := by
  simpa only [lowerScaleDiff, LowerScaleActionCoefficients.firstOrderCoefficientDifference] using
    lowerScaleActionCoefficients_zeroOrderCoefficient_sub (I := I) (M := M) g T U hδ_lt hδT hδU hδZ

theorem metricCorrection_sub_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ g_bg : SmoothRiemannianMetric I M)
        (P Q : SmoothCcTensor g 0 2),
        covariantJetNormSq (I := I) (M := M) g 2
            (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g g₁ g_bg P -
              metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g g₁ g_bg Q) ≤
          C * covariantJetNormSq (I := I) (M := M) g 2 (P - Q) *
            covariantJetNormSq (I := I) (M := M) g 2
              (metricLoweredConnectionDifference (I := I) (M := M) g g₁ g_bg) := by
  obtain ⟨C, hC, hmul⟩ :=
    metricLoweredConnectionDifferenceCorrection_sobolev_two_mul_bound (I := I) (M := M) hDim g
  refine ⟨C, hC, ?_⟩
  intro g₁ g_bg P Q
  rw [← metricLoweredConnectionDifferenceCorrection_sub (I := I) (M := M) g g₁ g_bg P Q]
  simpa only [covariantJetNormSq, Nat.reduceAdd] using hmul g₁ g_bg (P - Q)

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem metricCorrection_tel
    (g gT gU g_bg : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) :
    metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g_bg T -
        metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g_bg U =
      metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g_bg (T - U) +
        (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g_bg U -
          metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g_bg U) := by
  rw [metricLoweredConnectionDifferenceCorrection_sub (I := I) (M := M) g gT g_bg T U]
  abel

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem metricLoweredConnectionDifference_sub
    (g gT gU g_bg : SmoothRiemannianMetric I M) :
    metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg -
        metricLoweredConnectionDifference (I := I) (M := M) g gU g_bg =
      metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
        metricLoweredConnectionDifferenceCoefficient (I := I) g gU := by
  simp only [metricLoweredConnectionDifference]
  abel

omit [BoundarylessManifold I M] [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem jet_nonneg_lip
    (g : SmoothRiemannianMetric I M) {r s m : ℕ}
    (S : SmoothCcTensor g r s) :
    0 ≤ covariantJetNormSq (I := I) (M := M) g m S :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem jet_smul_lip
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g m (c • S) =
      c ^ 2 * covariantJetNormSq (I := I) (M := M) g m S := by
  unfold covariantJetNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [iteratedCovGrad_smul, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem jet_add_lip
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S V : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g m (S + V) ≤
      2 * (covariantJetNormSq (I := I) (M := M) g m S +
        covariantJetNormSq (I := I) (M := M) g m V) := by
  unfold covariantJetNormSq
  calc
    ∑ q ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g r s q (S + V)‖ ^ 2 ≤
        ∑ q ∈ Finset.range (m + 1),
          2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
      refine Finset.sum_le_sum fun q _ => ?_
      rw [iteratedCovGrad_add]
      have htri := norm_add_le
        (iteratedCovGrad (I := I) g r s q S)
        (iteratedCovGrad (I := I) g r s q V)
      calc
        ‖iteratedCovGrad (I := I) g r s q S +
            iteratedCovGrad (I := I) g r s q V‖ ^ 2 ≤
            (‖iteratedCovGrad (I := I) g r s q S‖ +
              ‖iteratedCovGrad (I := I) g r s q V‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
        _ ≤ 2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
          nlinarith only [sq_nonneg
            (‖iteratedCovGrad (I := I) g r s q S‖ -
              ‖iteratedCovGrad (I := I) g r s q V‖)]
    _ = 2 * ((∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s q S‖ ^ 2) +
        ∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]

theorem firstOrderCoefficientDifference_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B0 B1 : ℝ,
      0 < ρ ∧ 0 ≤ B0 ∧ 0 ≤ B1 ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ (1 : ℝ) / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (A D3 : ℝ), 0 ≤ A → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (firstOrderCoefficientDifference (I := I) (M := M) g T U
            (lt_of_le_of_lt hδ_le
              (by norm_num : (1 : ℝ) / 3 < 1))
            hδT hδU hδZ) ≤
        (B0 * D3 +
          B1 * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖ +
          B1 * A * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖) ^ 2 := by
  obtain ⟨ρ, B0, B1, hρ, hB0, hB1, hkernel⟩ :=
    ricciDeTurckRemainderFirstOrderCoefficient_pairing_h2_bound (I := I) (M := M) hDim g
  refine ⟨ρ, B0, B1, hρ, hB0, hB1, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    hTHs hUHs A D3 hA hD3 hT3 hTU3
  let hδ_lt : δ < 1 :=
    lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  let Φ : ℝ → SmoothCcTensor g 3 2 := fun s =>
    ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g T 0 hδT hδZ s -
      ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g U 0 hδU hδZ s
  let S : Set ℝ := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let B : ℝ := B0 * D3 + B1 * N + B1 * A * N
  have hN : 0 ≤ N := norm_nonneg _
  have hB : 0 ≤ B :=
    add_nonneg
      (add_nonneg (mul_nonneg hB0 hD3) (mul_nonneg hB1 hN))
      (mul_nonneg (mul_nonneg hB1 hA) hN)
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    dsimp only [S]
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hjoint :
      linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g 3 Φ
        (δ := δ) (δ' := δ) := by
    dsimp only [Φ]
    exact covariantJetJoint_sub (I := I) (M := M) g _ _
      (ricciDeTurckRemainderFirstOrderCoefficient_path_joint (I := I) (M := M)
        g g T 0 hδT hδZ)
      (ricciDeTurckRemainderFirstOrderCoefficient_path_joint (I := I) (M := M)
        g g U 0 hδU hδZ)
  have hpoint :
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        covariantJetNormSq (I := I) (M := M) g 2 (Φ s) ≤ B ^ 2 := by
    intro s hs
    let P : SmoothCcTensor g 0 2 := s • T
    let Q : SmoothCcTensor g 0 2 := s • U
    let gmT : SmoothRiemannianMetric I M :=
      metricPerturbationPath (I := I) g T 0 hδT hδZ s
    let gmU : SmoothRiemannianMetric I M :=
      metricPerturbationPath (I := I) g U 0 hδU hδZ s
    have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
      Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
    have hsabs : ‖s‖ ≤ (1 : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact hs.2
    have hs2 : s ^ 2 ≤ (1 : ℝ) := by
      nlinarith only [hs.1, hs.2]
    have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
        ccTensorBilin (I := I) g P x u v =
          ccTensorBilin (I := I) g P x v u := by
      intro x u v
      simp only [P, ccTensorBilin_apply, ccTensorModel_smul,
        smul_apply, smul_eq_mul]
      apply congrArg (fun z : ℝ => s * z)
      simpa only [ccTensorBilin_apply] using hT x u v
    have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
        ccTensorBilin (I := I) g Q x u v =
          ccTensorBilin (I := I) g Q x v u := by
      intro x u v
      simp only [Q, ccTensorBilin_apply, ccTensorModel_smul,
        smul_apply, smul_eq_mul]
      apply congrArg (fun z : ℝ => s * z)
      simpa only [ccTensorBilin_apply] using hU x u v
    have hPtie : ∀ (x : M) (u v : TangentSpace I x),
        gmT.inner x u v =
          g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
      intro x u v
      simpa only [gmT, P, convexPerturbation, smul_zero, zero_add] using
        metricPerturbationPath_inner_of_mem
          (I := I) g T 0 hδT hδZ hs_mem x u v
    have hQtie : ∀ (x : M) (u v : TangentSpace I x),
        gmU.inner x u v =
          g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
      intro x u v
      simpa only [gmU, Q, convexPerturbation, smul_zero, zero_add] using
        metricPerturbationPath_inner_of_mem
          (I := I) g U 0 hδU hδZ hs_mem x u v
    have hδP : gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g P) δ := by
      intro x u v
      have hraw :=
        convexPerturbation_gFibreOpBound_abs
          (I := I) g T 0 hδT hδZ s x u v
      have heq : |1 - s| * δ + |s| * δ = δ := by
        rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
          abs_of_nonneg hs.1]
        ring
      simpa only [P, convexPerturbation, smul_zero, zero_add, heq] using hraw
    have hδQ : gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g Q) δ := by
      intro x u v
      have hraw :=
        convexPerturbation_gFibreOpBound_abs
          (I := I) g U 0 hδU hδZ s x u v
      have heq : |1 - s| * δ + |s| * δ = δ := by
        rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
          abs_of_nonneg hs.1]
        ring
      simpa only [Q, convexPerturbation, smul_zero, zero_add, heq] using hraw
    have hPnorm :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ := by
      rw [show P = s • T from rfl, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using hTHs)
    have hQnorm :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ := by
      rw [show Q = s • U from rfl, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using hUHs)
    have hP3 :
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
      rw [show P = s • T from rfl, jet_smul_lip]
      calc
        s ^ 2 * covariantJetNormSq (I := I) (M := M) g 3 T ≤
            1 * covariantJetNormSq (I := I) (M := M) g 3 T :=
          mul_le_mul_of_nonneg_right hs2
            (jet_nonneg_lip (I := I) (M := M) g T)
        _ ≤ A ^ 2 := by simpa using hT3
    have hPQeq : P - Q = s • (T - U) := by
      dsimp only [P, Q]
      module
    have hPQ3 :
        covariantJetNormSq (I := I) (M := M) g 3 (P - Q) ≤ D3 ^ 2 := by
      rw [hPQeq, jet_smul_lip]
      calc
        s ^ 2 * covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤
            1 * covariantJetNormSq (I := I) (M := M) g 3 (T - U) :=
          mul_le_mul_of_nonneg_right hs2
            (jet_nonneg_lip (I := I) (M := M) g (T - U))
        _ ≤ D3 ^ 2 := by simpa using hTU3
    have hPQ2 :
        ‖ccTensorToHs (I := I) (M := M) g
          2 (2 : ℝ) (P - Q)‖ ≤ N := by
      rw [hPQeq, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs hN).trans (by simp)
    have hraw :
        covariantJetNormSq (I := I) (M := M) g 2
            ((-2 : ℝ) •
                (linearizedRicciConnectionDifferenceOrder1CoeffField
                    (I := I) (M := M) g gmT -
                  linearizedRicciConnectionDifferenceOrder1CoeffField
                    (I := I) (M := M) g gmU) +
              (deTurckLieFirstOrderCoeff (I := I) (M := M) g gmT g -
                deTurckLieFirstOrderCoeff (I := I) (M := M) g gmU g)) ≤
          (B0 * D3 +
            B1 * ‖ccTensorToHs (I := I) (M := M)
              g 2 (2 : ℝ) (P - Q)‖ +
            B1 * A * ‖ccTensorToHs (I := I) (M := M)
              g 2 (2 : ℝ) (P - Q)‖) ^ 2 := by
      simpa only [gmT, gmU] using
        hkernel gmT gmU P Q hPsymm hQsymm hPtie hQtie
          hδ_le hδ0 hδP hδQ hδZ hPnorm hQnorm
          A D3 hA hD3 hP3 hPQ3
    have hbase0 :
        0 ≤ B0 * D3 +
          B1 * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (P - Q)‖ +
          B1 * A * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (P - Q)‖ :=
      add_nonneg
        (add_nonneg (mul_nonneg hB0 hD3)
          (mul_nonneg hB1 (norm_nonneg _)))
        (mul_nonneg (mul_nonneg hB1 hA) (norm_nonneg _))
    have hbase :
        B0 * D3 +
            B1 * ‖ccTensorToHs (I := I) (M := M)
              g 2 (2 : ℝ) (P - Q)‖ +
            B1 * A * ‖ccTensorToHs (I := I) (M := M)
              g 2 (2 : ℝ) (P - Q)‖ ≤ B := by
      dsimp only [B]
      have h1 := mul_le_mul_of_nonneg_left hPQ2 hB1
      have h2 := mul_le_mul_of_nonneg_left hPQ2 (mul_nonneg hB1 hA)
      dsimp only [N] at h1 h2 ⊢
      linarith
    have hΦeq :
        Φ s =
          (-2 : ℝ) •
              (linearizedRicciConnectionDifferenceOrder1CoeffField
                  (I := I) (M := M) g gmT -
                linearizedRicciConnectionDifferenceOrder1CoeffField
                  (I := I) (M := M) g gmU) +
            (deTurckLieFirstOrderCoeff (I := I) (M := M) g gmT g -
              deTurckLieFirstOrderCoeff (I := I) (M := M) g gmU g) := by
      dsimp only [Φ, gmT, gmU]
      rw [rhsLow1_sub (I := I) (M := M) g T U hδT hδU hδZ s]
      rfl
    rw [hΦeq]
    exact hraw.trans (pow_le_pow_left₀ hbase0 hbase 2)
  have hpath := path_jetL2_le (I := I) (M := M)
    g 3 2 2 Φ S metricPerturbationPathDomain_isOpen hSI hjoint
    (B := B) hpoint
  simpa only [covariantJetNormSq, firstOrderCoefficientDifference, Φ, S, N, B, Nat.reduceAdd,
    hδ_lt] using hpath

theorem exists_lieCorrectionZeroRiemann_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) →
        (∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        covariantJetNormSq (I := I) (M := M) g 2
            (lieCorrectionZeroRiemann (I := I) (M := M) g gT -
              lieCorrectionZeroRiemann (I := I) (M := M) g gU) ≤
          (C * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖) ^ 2 := by
  obtain ⟨ρ, Ct, hρ, hCt, htrace⟩ :=
    RicciDeTurckLowOrder.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    operator_field_composition_h2_h2_to_h2_bound (I := I) (M := M) hDim g 2 4 2
  let JP : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (lieCorrectionZeroRiemannLift (I := I) g)
  let Pn : ℝ := Real.sqrt JP
  let C : ℝ := Ca * Ct * Pn
  have hJP : 0 ≤ JP :=
    jet_nonneg_lip (I := I) (M := M) g
      (lieCorrectionZeroRiemannLift (I := I) g)
  have hPn : 0 ≤ Pn := Real.sqrt_nonneg _
  have hPnsq : Pn ^ 2 = JP := by
    simpa only [Pn] using Real.sq_sqrt hJP
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg hCa hCt) hPn
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hTHs hUHs
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let L : SmoothCcTensor g 4 2 :=
    reindexedCometricDoubleTrace (I := I) (M := M) g gT -
      reindexedCometricDoubleTrace (I := I) (M := M) g gU
  have hN : 0 ≤ N := norm_nonneg _
  have hL :
      covariantJetNormSq (I := I) (M := M) g 2 L ≤ (Ct * N) ^ 2 := by
    rw [show L =
      pureTrace (I := I) (M := M) g gT 2 -
        pureTrace (I := I) (M := M) g gU 2 by
          simp only [L, reindexedCometricDoubleTrace_eq_pureTrace]]
    simpa only [N] using
      htrace T U gT gU hTtie hUtie hTHs hUHs
  have hApp :
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 2 4 2 L
            (lieCorrectionZeroRiemannLift (I := I) g)) ≤
        (Ca * (Ct * N) * Pn) ^ 2 := by
    simpa only [covariantJetNormSq, JP] using
      happ L (lieCorrectionZeroRiemannLift (I := I) g) (Ct * N) Pn
        (mul_nonneg hCt hN) hPn hL
        (by
          simpa only [covariantJetNormSq, JP] using
            (le_of_eq hPnsq.symm))
  have heq :
      lieCorrectionZeroRiemann (I := I) (M := M) g gT -
          lieCorrectionZeroRiemann (I := I) (M := M) g gU =
        -ccOperatorFieldComp (I := I) (M := M) g 2 4 2 L
          (lieCorrectionZeroRiemannLift (I := I) g) := by
    rw [lieCorrectionZeroRiemann_eq_ccOperatorFieldComp, lieCorrectionZeroRiemann_eq_ccOperatorFieldComp]
    dsimp only [L]
    rw [operatorFieldComposition_sub_left]
    module
  rw [heq, show -ccOperatorFieldComp (I := I) (M := M) g 2 4 2 L
      (lieCorrectionZeroRiemannLift (I := I) g) =
        (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 4 2 L
          (lieCorrectionZeroRiemannLift (I := I) g) by simp,
    jet_smul_lip]
  norm_num
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g 2 4 2 L
          (lieCorrectionZeroRiemannLift (I := I) g)) ≤
      (Ca * (Ct * N) * Pn) ^ 2 := hApp
    _ = (C * N) ^ 2 := by
      dsimp only [C]
      ring

private theorem lieSecondOrder_jet_le
    (g gT gU : SmoothRiemannianMetric I M) :
    covariantJetNormSq (I := I) (M := M) g 2
        (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT -
          deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gU) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g) := by
  let fr : ℝ := Module.finrank ℝ E
  have hper : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 3 4 q
          (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT -
            deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gU)‖ ^ 2 ≤
        fr ^ 2 *
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connectionDifferenceSection (I := I) gT g -
              connectionDifferenceSection (I := I) gU g)‖ ^ 2 := by
    intro q
    let F : M → ℝ := fun x => fr ^ 2 *
      riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
        ((iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g)).toSection x)
    have hF : MeasureTheory.Integrable F
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      dsimp only [F]
      exact (integrable_riemannianFiberNormSq_toSection
        (I := I) (M := M) g 1 (2 + q)
        (iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g))).const_mul _
    have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g 3 (4 + q)
      (iteratedCovGrad (I := I) g 3 4 q
        (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT -
          deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gU))
      F hF (fun x => by
        simpa only [F, fr] using
          deTurckLieCovariantDerivativeSecondOrderCoefficient_sub_l2 (I := I) (M := M) g gT gU q x)
    have hint : (∫ x,
        riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
          ((iteratedCovGrad (I := I) g 1 2 q
            (connectionDifferenceSection (I := I) gT g -
              connectionDifferenceSection (I := I) gU g)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connectionDifferenceSection (I := I) gT g -
              connectionDifferenceSection (I := I) gU g)‖ ^ 2 := by
      rw [SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
    dsimp only [F] at hsq
    rw [MeasureTheory.integral_const_mul, hint] at hsq
    exact hsq
  unfold covariantJetNormSq
  calc
    ∑ q ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 3 4 q
          (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT -
            deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gU)‖ ^ 2 ≤
      ∑ q ∈ Finset.range 3, fr ^ 2 *
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g)‖ ^ 2 :=
      Finset.sum_le_sum fun q _ => hper q
    _ = fr ^ 2 * ∑ q ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g)‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem lieSecondOrder_jet1_le
    (g gT gU : SmoothRiemannianMetric I M) :
    covariantJetNormSq (I := I) (M := M) g 1
        (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT -
          deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gU) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 1
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g) := by
  let fr : ℝ := Module.finrank ℝ E
  have hper : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 3 4 q
          (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT -
            deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gU)‖ ^ 2 ≤
        fr ^ 2 *
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connectionDifferenceSection (I := I) gT g -
              connectionDifferenceSection (I := I) gU g)‖ ^ 2 := by
    intro q
    let F : M → ℝ := fun x => fr ^ 2 *
      riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
        ((iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g)).toSection x)
    have hF : MeasureTheory.Integrable F
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      dsimp only [F]
      exact (integrable_riemannianFiberNormSq_toSection
        (I := I) (M := M) g 1 (2 + q)
        (iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g))).const_mul _
    have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g 3 (4 + q)
      (iteratedCovGrad (I := I) g 3 4 q
        (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT -
          deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gU))
      F hF (fun x => by
        simpa only [F, fr] using
          deTurckLieCovariantDerivativeSecondOrderCoefficient_sub_l2 (I := I) (M := M) g gT gU q x)
    have hint : (∫ x,
        riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
          ((iteratedCovGrad (I := I) g 1 2 q
            (connectionDifferenceSection (I := I) gT g -
              connectionDifferenceSection (I := I) gU g)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connectionDifferenceSection (I := I) gT g -
              connectionDifferenceSection (I := I) gU g)‖ ^ 2 := by
      rw [SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
    dsimp only [F] at hsq
    rw [MeasureTheory.integral_const_mul, hint] at hsq
    exact hsq
  unfold covariantJetNormSq
  calc
    ∑ q ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 3 4 q
          (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT -
            deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gU)‖ ^ 2 ≤
      ∑ q ∈ Finset.range 2, fr ^ 2 *
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g)‖ ^ 2 :=
      Finset.sum_le_sum fun q _ => hper q
    _ = fr ^ 2 * ∑ q ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g)‖ ^ 2 := by
      rw [Finset.mul_sum]

theorem lieSecondOrder_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ 1 / 3) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ 1 / 3) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT -
            deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gU) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨C0, C1, hC0, hC1, hconn⟩ :=
    connSec_sub_tame (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let fr : ℝ := Module.finrank ℝ E
  let B0 : ℝ → ℝ := fun R => fr * C0 R
  let B1 : ℝ → ℝ := fun R => fr * C1 R
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨B0, B1, fun R hR => mul_nonneg hfr (hC0 R hR),
    fun R hR => mul_nonneg hfr (hC1 R hR), ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  let X : ℝ := C0 R * D3 + C1 R * D2 + C1 R * A * D2
  have hC :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g) ≤ X ^ 2 := by
    simpa only [X] using
      hconn gT gU T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT -
          deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gU) ≤
      fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceSection (I := I) gT g -
          connectionDifferenceSection (I := I) gU g) := by
            simpa only [fr] using
              lieSecondOrder_jet_le (I := I) (M := M) g gT gU
    _ ≤ fr ^ 2 * X ^ 2 :=
      mul_le_mul_of_nonneg_left hC (sq_nonneg fr)
    _ = (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
      simp only [B0, B1, X]
      ring

theorem lieSecondOrder_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ 1 / 3) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ 1 / 3) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT -
            deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gU) ≤
        (B0 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨C0, C1, hC0, hC1, hconn⟩ :=
    connSec_pair_h1 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let fr : ℝ := Module.finrank ℝ E
  let B0 : ℝ → ℝ := fun R => fr * C0 R
  let B1 : ℝ → ℝ := fun R => fr * C1 R
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨B0, B1, fun R hR => mul_nonneg hfr (hC0 R hR),
    fun R hR => mul_nonneg hfr (hC1 R hR), ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 hR hA hD2 hU2 hT3 hTU2
  let X : ℝ := C0 R * D2 + C1 R * A * D2
  have hC :
      covariantJetNormSq (I := I) (M := M) g 1
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g) ≤ X ^ 2 := by
    simpa only [X] using
      hconn gT gU T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU
        R A D2 hR hA hD2 hU2 hT3 hTU2
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT -
          deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gU) ≤
      fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 1
        (connectionDifferenceSection (I := I) gT g -
          connectionDifferenceSection (I := I) gU g) := by
            simpa only [fr] using
              lieSecondOrder_jet1_le (I := I) (M := M) g gT gU
    _ ≤ fr ^ 2 * X ^ 2 :=
      mul_le_mul_of_nonneg_left hC (sq_nonneg fr)
    _ = (B0 R * D2 + B1 R * A * D2) ^ 2 := by
      simp only [B0, B1, X]
      ring

theorem metricCorrection_pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU g_bg : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2),
        covariantJetNormSq (I := I) (M := M) g 2
            (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g_bg T -
              metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g_bg U) ≤
          C *
            (covariantJetNormSq (I := I) (M := M) g 2 (T - U) *
                covariantJetNormSq (I := I) (M := M) g 2
                  (metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg) +
              covariantJetNormSq (I := I) (M := M) g 2 U *
                covariantJetNormSq (I := I) (M := M) g 2
                  (metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg -
                    metricLoweredConnectionDifference (I := I) (M := M) g gU g_bg)) := by
  obtain ⟨C₀, hC₀, hsub⟩ :=
    metricCorrection_sub_h2 (I := I) (M := M) hDim g
  obtain ⟨C₁, hC₁, hmove⟩ :=
    metricLoweredConnectionDifferenceCorrection_metric_difference_sobolev_two_bound (I := I) (M := M) hDim g
  let C : ℝ := 2 * max C₀ C₁
  have hCmax : 0 ≤ max C₀ C₁ := hC₀.trans (le_max_left C₀ C₁)
  refine ⟨C, mul_nonneg (by norm_num) hCmax, ?_⟩
  intro gT gU g_bg T U
  let X : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g_bg (T - U)
  let Y : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g_bg U -
      metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g_bg U
  let A : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2 (T - U) *
      covariantJetNormSq (I := I) (M := M) g 2
        (metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg)
  let B : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2 U *
      covariantJetNormSq (I := I) (M := M) g 2
        (metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg -
          metricLoweredConnectionDifference (I := I) (M := M) g gU g_bg)
  have hA : 0 ≤ A := mul_nonneg
    (jet_nonneg_lip (I := I) (M := M) g (T - U))
    (jet_nonneg_lip (I := I) (M := M) g
      (metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg))
  have hB : 0 ≤ B := mul_nonneg
    (jet_nonneg_lip (I := I) (M := M) g U)
    (jet_nonneg_lip (I := I) (M := M) g
      (metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg -
        metricLoweredConnectionDifference (I := I) (M := M) g gU g_bg))
  have hX :
      covariantJetNormSq (I := I) (M := M) g 2 X ≤ C₀ * A := by
    have hXraw := hsub gT g_bg T U
    rw [← metricLoweredConnectionDifferenceCorrection_sub (I := I) (M := M) g gT g_bg T U] at hXraw
    simpa only [X, A, mul_assoc] using hXraw
  have hY :
      covariantJetNormSq (I := I) (M := M) g 2 Y ≤ C₁ * B := by
    have hYraw := hmove gT gU g_bg U
    change covariantJetNormSq (I := I) (M := M) g 2
        (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g_bg U -
          metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g_bg U) ≤
      C₁ * covariantJetNormSq (I := I) (M := M) g 2 U *
        covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg -
            metricLoweredConnectionDifference (I := I) (M := M) g gU g_bg) at hYraw
    simpa only [Y, B, mul_assoc] using hYraw
  have hC₀max : C₀ * A ≤ max C₀ C₁ * A :=
    mul_le_mul_of_nonneg_right (le_max_left C₀ C₁) hA
  have hC₁max : C₁ * B ≤ max C₀ C₁ * B :=
    mul_le_mul_of_nonneg_right (le_max_right C₀ C₁) hB
  rw [metricCorrection_tel (I := I) (M := M) g gT gU g_bg T U]
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (X + Y) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
          covariantJetNormSq (I := I) (M := M) g 2 Y) :=
      jet_add_lip (I := I) (M := M) g 2 X Y
    _ ≤ 2 * (C₀ * A + C₁ * B) :=
      mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ ≤ 2 * (max C₀ C₁ * A + max C₀ C₁ * B) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hC₀max hC₁max) (by norm_num)
    _ = C * (A + B) := by
      simp only [C]
      ring

omit [BoundarylessManifold I M] [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem jet_mono_lip
    (g : SmoothRiemannianMetric I M) {r s m n : ℕ}
    (hmn : m ≤ n) (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g m S ≤
      covariantJetNormSq (I := I) (M := M) g n S := by
  unfold covariantJetNormSq
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (Nat.add_le_add_right hmn 1))
    (fun _ _ _ => sq_nonneg _)

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem iteratedCovGrad_zero_lip
    (g : SmoothRiemannianMetric I M) (r s m : ℕ) :
    iteratedCovGrad (I := I) g r s m
        (0 : SmoothCcTensor g r s) = 0 := by
  induction m with
  | zero => rw [iteratedCovGrad_zero]
  | succ m ih => rw [iteratedCovGrad_succ, ih, covGrad_zero]

omit [CompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem jet_zero_lip
    (g : SmoothRiemannianMetric I M) {r s m : ℕ} :
    covariantJetNormSq (I := I) (M := M) g m
        (0 : SmoothCcTensor g r s) = 0 := by
  unfold covariantJetNormSq
  apply Finset.sum_eq_zero
  intro q hq
  rw [iteratedCovGrad_zero_lip, norm_zero, zero_pow (by norm_num)]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem wXi_zero_lip
    (g : SmoothRiemannianMetric I M) :
    metricLoweredConnectionDifference (I := I) (M := M) g g g = 0 := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  apply ContinuousMultilinearMap.ext
  intro m
  have hm : m = fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m i)) := by
    funext i
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [hm, metricLoweredConnectionDifference_unitModel_apply]
  simp only [PDE.DeTurck.connectionDifference_self, Pi.zero_apply,
    zero_apply, map_zero]
  rfl

theorem metricCorrection_pair_h3
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g T -
            metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 2 *
          (1 + covariantJetNormSq (I := I) (M := M) g 3 U) ^ 2 *
          covariantJetNormSq (I := I) (M := M) g 3 (T - U) := by
  obtain ⟨C, hC, hpair⟩ :=
    metricCorrection_pair (I := I) (M := M) hDim g
  obtain ⟨Kw, hKw, hw⟩ :=
    exists_metricLoweredConnectionDifference_covariantJetNormSq_two_sub_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let K : ℝ := 2 * C * Kw
  refine ⟨K, mul_nonneg (mul_nonneg (by norm_num) hC) hKw, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0
    hδT hδU hδZ
  let JT : ℝ := covariantJetNormSq (I := I) (M := M) g 3 T
  let JU : ℝ := covariantJetNormSq (I := I) (M := M) g 3 U
  let JD : ℝ := covariantJetNormSq (I := I) (M := M) g 3 (T - U)
  let WT : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (metricLoweredConnectionDifference (I := I) (M := M) g gT g)
  let WD : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (metricLoweredConnectionDifference (I := I) (M := M) g gT g -
      metricLoweredConnectionDifference (I := I) (M := M) g gU g)
  let A : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2 (T - U) * WT
  let B : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2 U * WD
  let P : ℝ := (1 + JT) ^ 2 * (1 + JU) ^ 2
  have hZsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x u v =
        ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero, ccTensorBilin_zero]
  have hZtie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v =
        g.inner x u v +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero,
      ccTensorBilin_zero]
    ring
  have hJT : 0 ≤ JT := jet_nonneg_lip (I := I) (M := M) g T
  have hJU : 0 ≤ JU := jet_nonneg_lip (I := I) (M := M) g U
  have hJD : 0 ≤ JD := jet_nonneg_lip (I := I) (M := M) g (T - U)
  have hWT : 0 ≤ WT :=
    jet_nonneg_lip (I := I) (M := M) g
      (metricLoweredConnectionDifference (I := I) (M := M) g gT g)
  have hWD : 0 ≤ WD :=
    jet_nonneg_lip (I := I) (M := M) g
      (metricLoweredConnectionDifference (I := I) (M := M) g gT g -
        metricLoweredConnectionDifference (I := I) (M := M) g gU g)
  have hwTraw := hw gT g g T (0 : SmoothCcTensor g 0 2)
    hT hZsymm hTtie hZtie
    hδ_le hδ0 hδT hδ_le hδ0 hδZ
  have hwT : WT ≤ Kw * (1 + JT) * JT := by
    simpa only [WT, JT, wXi_zero_lip, sub_zero, jet_zero_lip,
      add_zero, one_mul, mul_one] using hwTraw
  have hwD : WD ≤ Kw * (1 + JT) * (1 + JU) * JD := by
    simpa only [WD, JT, JU, JD] using
      hw gT gU g T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
  have hD2 : covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ JD := by
    simpa only [JD] using
      jet_mono_lip (I := I) (M := M) g (by omega : 2 ≤ 3) (T - U)
  have hU2 : covariantJetNormSq (I := I) (M := M) g 2 U ≤ JU := by
    simpa only [JU] using
      jet_mono_lip (I := I) (M := M) g (by omega : 2 ≤ 3) U
  have hPA : (1 + JT) * JT ≤ P := by
    have hJT1 : JT ≤ 1 + JT := by linarith
    have h1JT : 0 ≤ 1 + JT := by linarith
    have h1U : 1 ≤ (1 + JU) ^ 2 := by nlinarith only [hJU]
    calc
      (1 + JT) * JT ≤ (1 + JT) * (1 + JT) :=
        mul_le_mul_of_nonneg_left hJT1 h1JT
      _ = ((1 + JT) * (1 + JT)) * 1 := by ring
      _ ≤ ((1 + JT) * (1 + JT)) * (1 + JU) ^ 2 :=
        mul_le_mul_of_nonneg_left h1U (mul_nonneg h1JT h1JT)
      _ = P := by simp only [P, pow_two]
  have hPB : (1 + JT) * (1 + JU) * JU ≤ P := by
    have hJU1 : JU ≤ 1 + JU := by linarith
    have h1JT : 0 ≤ 1 + JT := by linarith
    have h1JU : 0 ≤ 1 + JU := by linarith
    have hJT1 : 1 ≤ 1 + JT := by linarith
    have hJTsq : 1 + JT ≤ (1 + JT) ^ 2 := by
      calc
        1 + JT = (1 + JT) * 1 := by ring
        _ ≤ (1 + JT) * (1 + JT) :=
          mul_le_mul_of_nonneg_left hJT1 h1JT
        _ = (1 + JT) ^ 2 := by ring
    calc
      (1 + JT) * (1 + JU) * JU ≤
          (1 + JT) * (1 + JU) * (1 + JU) :=
        mul_le_mul_of_nonneg_left hJU1 (mul_nonneg h1JT h1JU)
      _ = (1 + JT) * (1 + JU) ^ 2 := by ring
      _ ≤ (1 + JT) ^ 2 * (1 + JU) ^ 2 :=
        mul_le_mul_of_nonneg_right hJTsq (sq_nonneg _)
      _ = P := rfl
  have hA : A ≤ Kw * P * JD := by
    have hraw : A ≤ JD * (Kw * (1 + JT) * JT) := by
      exact mul_le_mul hD2 hwT hWT hJD
    calc
      A ≤ JD * (Kw * (1 + JT) * JT) := hraw
      _ = Kw * ((1 + JT) * JT) * JD := by ring
      _ ≤ Kw * P * JD :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPA hKw) hJD
  have hB : B ≤ Kw * P * JD := by
    have hraw : B ≤ JU * (Kw * (1 + JT) * (1 + JU) * JD) := by
      exact mul_le_mul hU2 hwD hWD hJU
    calc
      B ≤ JU * (Kw * (1 + JT) * (1 + JU) * JD) := hraw
      _ = Kw * ((1 + JT) * (1 + JU) * JU) * JD := by ring
      _ ≤ Kw * P * JD :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPB hKw) hJD
  have hAB : A + B ≤ 2 * (Kw * P * JD) := by
    linarith
  have hraw := hpair gT gU g T U
  change covariantJetNormSq (I := I) (M := M) g 2
      (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g T -
        metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U) ≤
    C * (A + B) at hraw
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g T -
          metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U) ≤
      C * (A + B) := hraw
    _ ≤ C * (2 * (Kw * P * JD)) :=
      mul_le_mul_of_nonneg_left hAB hC
    _ = K * P * JD := by
      simp only [K]
      ring
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 2 *
        (1 + covariantJetNormSq (I := I) (M := M) g 3 U) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) := by
      simp only [P, JT, JU, JD]
      ring

private theorem wXi_self_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g) ≤
        (B R * A) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hw⟩ :=
    exists_metricLoweredConnectionDifference_covariantJetNormSq_two_sub_tame_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let B : ℝ → ℝ := fun R => B0 0 + B1 0 + B1 0 * R
  refine ⟨B, ?_, ?_⟩
  · intro R hR
    exact add_nonneg
      (add_nonneg (hB0 0 (by norm_num)) (hB1 0 (by norm_num)))
      (mul_nonneg (hB1 0 (by norm_num)) hR)
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  let J2 : ℝ := covariantJetNormSq (I := I) (M := M) g 2 T
  let D2 : ℝ := Real.sqrt J2
  have hJ2 : 0 ≤ J2 :=
    jet_nonneg_lip (I := I) (M := M) g T
  have hD2 : 0 ≤ D2 := Real.sqrt_nonneg _
  have hD2sq : D2 ^ 2 = J2 := by
    simpa only [D2] using Real.sq_sqrt hJ2
  have hJ23 : J2 ≤ covariantJetNormSq (I := I) (M := M) g 3 T := by
    simpa only [J2] using
      jet_mono_lip (I := I) (M := M) g (by omega : 2 ≤ 3) T
  have hD2A : D2 ≤ A := by
    nlinarith only [hD2sq, hJ23, hT3, hD2, hA]
  have hD2R : D2 ≤ R := by
    have : J2 ≤ R ^ 2 := by simpa only [J2] using hT2
    nlinarith only [hD2sq, this, hD2, hR]
  have hZsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x u v =
        ccTensorBilin (I := I) g
          (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero, ccTensorBilin_zero]
  have hZtie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v =
        g.inner x u v +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero,
      ccTensorBilin_zero]
    ring
  have hraw := hw gT g g T (0 : SmoothCcTensor g 0 2)
    hT hZsymm hTtie hZtie
    hδ_le hδ0 hδT hδ_le hδ0 hδZ
    0 A D2 A (by norm_num) hA hD2 hA
    (by
      rw [jet_zero_lip]
      norm_num)
    hT3
    (by
      rw [sub_zero]
      change J2 ≤ D2 ^ 2
      rw [hD2sq])
    (by simpa only [sub_zero] using hT3)
  have hraw' :
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g) ≤
        (B0 0 * A + B1 0 * D2 + B1 0 * A * D2) ^ 2 := by
    simpa only [wXi_zero_lip, sub_zero] using hraw
  have hB00 : 0 ≤ B0 0 := hB0 0 (by norm_num)
  have hB10 : 0 ≤ B1 0 := hB1 0 (by norm_num)
  have hmid : B1 0 * D2 ≤ B1 0 * A :=
    mul_le_mul_of_nonneg_left hD2A hB10
  have hlast : B1 0 * A * D2 ≤ B1 0 * A * R :=
    mul_le_mul_of_nonneg_left hD2R (mul_nonneg hB10 hA)
  have hlin :
      B0 0 * A + B1 0 * D2 + B1 0 * A * D2 ≤ B R * A := by
    simp only [B]
    nlinarith only [hmid, hlast]
  have hlin0 :
      0 ≤ B0 0 * A + B1 0 * D2 + B1 0 * A * D2 :=
    add_nonneg
      (add_nonneg (mul_nonneg hB00 hA) (mul_nonneg hB10 hD2))
      (mul_nonneg (mul_nonneg hB10 hA) hD2)
  exact hraw'.trans (pow_le_pow_left₀ hlin0 hlin 2)

private theorem lieSecondOrder_self_le
    (g gT : SmoothRiemannianMetric I M) :
    covariantJetNormSq (I := I) (M := M) g 2
        (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gT g) := by
  let fr : ℝ := Module.finrank ℝ E
  have hper : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 3 4 q
          (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT)‖ ^ 2 ≤
        fr ^ 2 *
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connectionDifferenceSection (I := I) gT g)‖ ^ 2 := by
    intro q
    let F : M → ℝ := fun x => fr ^ 2 *
      riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
        ((iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) gT g)).toSection x)
    have hF : MeasureTheory.Integrable F
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      dsimp only [F]
      exact (integrable_riemannianFiberNormSq_toSection
        (I := I) (M := M) g 1 (2 + q)
        (iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) gT g))).const_mul _
    have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g 3 (4 + q)
      (iteratedCovGrad (I := I) g 3 4 q
        (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT))
      F hF (fun x => by
        simpa only [F, fr] using
          deTurckLieCovariantDerivativeSecondOrderCoefficient_l2 (I := I) (M := M) g gT q x)
    have hint : (∫ x,
        riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
          ((iteratedCovGrad (I := I) g 1 2 q
            (connectionDifferenceSection (I := I) gT g)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connectionDifferenceSection (I := I) gT g)‖ ^ 2 := by
      rw [SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
    dsimp only [F] at hsq
    rw [MeasureTheory.integral_const_mul, hint] at hsq
    exact hsq
  unfold covariantJetNormSq
  calc
    ∑ q ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 3 4 q
          (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT)‖ ^ 2 ≤
      ∑ q ∈ Finset.range 3, fr ^ 2 *
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) gT g)‖ ^ 2 :=
      Finset.sum_le_sum fun q _ => hper q
    _ = fr ^ 2 * ∑ q ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) gT g)‖ ^ 2 := by
      rw [Finset.mul_sum]

theorem deTurck_lie_term_two_coefficient_sobolev_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT) ≤
        (B R * A) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ :=
    lieSecondOrder_pair_h2 (I := I) (M := M) hDim g
  let H2 : ℝ := Real.sqrt 2
  let B : ℝ → ℝ := fun R =>
    H2 * (B0 0 + B1 0 + B1 0 * R)
  have hH2 : 0 ≤ H2 := Real.sqrt_nonneg _
  have hH2sq : H2 ^ 2 = (2 : ℝ) := by
    simpa only [H2] using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hB00 : 0 ≤ B0 0 := hB0 0 (by norm_num)
  have hB10 : 0 ≤ B1 0 := hB1 0 (by norm_num)
  refine ⟨B, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg hH2
      (add_nonneg (add_nonneg hB00 hB10) (mul_nonneg hB10 hR))
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  let J2 : ℝ := covariantJetNormSq (I := I) (M := M) g 2 T
  let D2 : ℝ := Real.sqrt J2
  let X : ℝ := B0 0 * A + B1 0 * D2 + B1 0 * A * D2
  let L : ℝ := (B0 0 + B1 0 + B1 0 * R) * A
  have hJ2 : 0 ≤ J2 :=
    jet_nonneg_lip (I := I) (M := M) g T
  have hD2 : 0 ≤ D2 := Real.sqrt_nonneg _
  have hD2sq : D2 ^ 2 = J2 := by
    simpa only [D2] using Real.sq_sqrt hJ2
  have hJ23 : J2 ≤ covariantJetNormSq (I := I) (M := M) g 3 T := by
    simpa only [J2] using
      jet_mono_lip (I := I) (M := M) g (by omega : 2 ≤ 3) T
  have hD2A : D2 ≤ A := by
    nlinarith only [hD2sq, hJ23, hT3, hD2, hA]
  have hD2R : D2 ≤ R := by
    have : J2 ≤ R ^ 2 := by simpa only [J2] using hT2
    nlinarith only [hD2sq, this, hD2, hR]
  have hZsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x u v =
        ccTensorBilin (I := I) g
          (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero, ccTensorBilin_zero]
  have hZtie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v =
        g.inner x u v +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero,
      ccTensorBilin_zero]
    ring
  have hdiff :
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT -
            deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g g) ≤ X ^ 2 := by
    simpa only [X] using
      hpair gT g T (0 : SmoothCcTensor g 0 2)
        hT hZsymm hTtie hZtie
        hδ_le hδ0 hδT hδ_le hδ0 hδZ
        0 A D2 A (by norm_num) hA hD2 hA
        (by rw [jet_zero_lip]; norm_num)
        hT3
        (by
          rw [sub_zero]
          change J2 ≤ D2 ^ 2
          rw [hD2sq])
        (by simpa only [sub_zero] using hT3)
  have hbase :
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g g) = 0 := by
    apply le_antisymm
    · calc
        covariantJetNormSq (I := I) (M := M) g 2
            (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g g) ≤
          (Module.finrank ℝ E : ℝ) ^ 2 *
            covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceSection (I := I) g g) :=
          lieSecondOrder_self_le (I := I) (M := M) g g
        _ = 0 := by
          rw [connectionDifferenceSection_self, jet_zero_lip, mul_zero]
    · exact jet_nonneg_lip (I := I) (M := M) g _
  have hX0 : 0 ≤ X := by
    exact add_nonneg
      (add_nonneg (mul_nonneg hB00 hA) (mul_nonneg hB10 hD2))
      (mul_nonneg (mul_nonneg hB10 hA) hD2)
  have hXL : X ≤ L := by
    simp only [X, L]
    have hmid : B1 0 * D2 ≤ B1 0 * A :=
      mul_le_mul_of_nonneg_left hD2A hB10
    have hlast : B1 0 * A * D2 ≤ B1 0 * A * R :=
      mul_le_mul_of_nonneg_left hD2R (mul_nonneg hB10 hA)
    nlinarith only [hmid, hlast]
  have hsplit :
      deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT =
        (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT -
          deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g g) +
        deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g g := by
    module
  rw [hsplit]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        ((deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT -
          deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g g) +
          deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g g) ≤
      2 * (covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g gT -
            deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g g) +
        covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeSecondOrderCoefficient (I := I) (M := M) g g)) :=
      jet_add_lip (I := I) (M := M) g 2 _ _
    _ ≤ 2 * (X ^ 2 + 0) :=
      mul_le_mul_of_nonneg_left (add_le_add hdiff (le_of_eq hbase))
        (by norm_num)
    _ ≤ 2 * L ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [add_zero] using pow_le_pow_left₀ hX0 hXL 2)
        (by norm_num)
    _ = (B R * A) ^ 2 := by
      simp only [B, L]
      rw [← hH2sq]
      ring

private theorem app_h2_mul_lip
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
    jet_nonneg_lip (I := I) (M := M) g Φ
  have hW0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 W :=
    jet_nonneg_lip (I := I) (M := M) g W
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

omit [NeZero (Module.finrank ℝ E)] in
private theorem dom_h2_lip
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    covariantJetNormSq (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g σ S) =
      covariantJetNormSq (I := I) (M := M) g 2 S := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro q _
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g σ S q x

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem dom_sub_lip
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : SmoothCcTensor g 0 s) :
    domDomCongrSection (I := I) g σ (A - B) =
      domDomCongrSection (I := I) g σ A -
        domDomCongrSection (I := I) g σ B := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  have hsub : ∀ (P Q : SmoothCcTensor g 0 s),
      unitModel (I := I) (M := M) g s (P - Q) x =
        unitModel (I := I) (M := M) g s P x -
          unitModel (I := I) (M := M) g s Q x := by
    intro P Q
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_sub]
    rfl
  rw [domDomCongrSection_unitModel, hsub A B]
  rw [hsub
    (domDomCongrSection (I := I) g σ A)
    (domDomCongrSection (I := I) g σ B)]
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [sub_apply,
    ContinuousMultilinearMap.domDomCongr_apply]

private noncomputable def lipOmega
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 0 3 :=
  ccOperatorFieldComp (I := I) (M := M) g 0 3 3
    (slotInsertEndoCc (I := I) (M := M) g 2
      (metricComparisonEndomorphismField (I := I) (M := M) gm g))
    (domDomCongrSection (I := I) g (finRotate 3)
      (metricLoweredConnectionDifferenceCoefficient (I := I) g gm))

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lipOmega_tel
    (g gT gU : SmoothRiemannianMetric I M) :
    lipOmega (I := I) (M := M) g gT -
        lipOmega (I := I) (M := M) g gU =
      ccOperatorFieldComp (I := I) (M := M) g 0 3 3
          (slotInsertEndoCc (I := I) (M := M) g 2
            (metricComparisonEndomorphismField (I := I) (M := M) gU g))
          (domDomCongrSection (I := I) g (finRotate 3)
            (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
              metricLoweredConnectionDifferenceCoefficient (I := I) g gU)) +
        ccOperatorFieldComp (I := I) (M := M) g 0 3 3
          (slotInsertEndoCc (I := I) (M := M) g 2
              (metricComparisonEndomorphismField (I := I) (M := M) gT g) -
            slotInsertEndoCc (I := I) (M := M) g 2
              (metricComparisonEndomorphismField (I := I) (M := M) gU g))
          (domDomCongrSection (I := I) g (finRotate 3)
            (metricLoweredConnectionDifferenceCoefficient (I := I) g gT)) := by
  rw [lipOmega, lipOmega, dom_sub_lip,
    operatorFieldComposition_sub_right, operatorFieldComposition_sub_left]
  module

private theorem omega_pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M),
        covariantJetNormSq (I := I) (M := M) g 2
            (lipOmega (I := I) (M := M) g gT -
              lipOmega (I := I) (M := M) g gU) ≤
          C *
            (covariantJetNormSq (I := I) (M := M) g 2
                (slotInsertEndoCc (I := I) (M := M) g 2
                  (metricComparisonEndomorphismField (I := I) (M := M) gU g)) *
              covariantJetNormSq (I := I) (M := M) g 2
                (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
                  metricLoweredConnectionDifferenceCoefficient (I := I) g gU) +
            covariantJetNormSq (I := I) (M := M) g 2
                (slotInsertEndoCc (I := I) (M := M) g 2
                    (metricComparisonEndomorphismField (I := I) (M := M) gT g) -
                  slotInsertEndoCc (I := I) (M := M) g 2
                    (metricComparisonEndomorphismField (I := I) (M := M) gU g)) *
              covariantJetNormSq (I := I) (M := M) g 2
                (metricLoweredConnectionDifferenceCoefficient (I := I) g gT)) := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    app_h2_mul_lip (I := I) (M := M) hDim g 0 3 3
  refine ⟨2 * C₀, mul_nonneg (by norm_num) hC₀, ?_⟩
  intro gT gU
  let AU : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2
      (metricComparisonEndomorphismField (I := I) (M := M) gU g)
  let AD : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M) gT g) -
      slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M) gU g)
  let BD : SmoothCcTensor g 0 3 :=
    domDomCongrSection (I := I) g (finRotate 3)
      (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
        metricLoweredConnectionDifferenceCoefficient (I := I) g gU)
  let BT : SmoothCcTensor g 0 3 :=
    domDomCongrSection (I := I) g (finRotate 3)
      (metricLoweredConnectionDifferenceCoefficient (I := I) g gT)
  let X : SmoothCcTensor g 0 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 0 3 3 AU BD
  let Y : SmoothCcTensor g 0 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 0 3 3 AD BT
  have hX :
      covariantJetNormSq (I := I) (M := M) g 2 X ≤
        C₀ * covariantJetNormSq (I := I) (M := M) g 2 AU *
          covariantJetNormSq (I := I) (M := M) g 2
            (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
              metricLoweredConnectionDifferenceCoefficient (I := I) g gU) := by
    have hraw := happ AU BD
    rw [dom_h2_lip] at hraw
    simpa only [X, BD] using hraw
  have hY :
      covariantJetNormSq (I := I) (M := M) g 2 Y ≤
        C₀ * covariantJetNormSq (I := I) (M := M) g 2 AD *
          covariantJetNormSq (I := I) (M := M) g 2
            (metricLoweredConnectionDifferenceCoefficient (I := I) g gT) := by
    have hraw := happ AD BT
    rw [dom_h2_lip] at hraw
    simpa only [Y, BT] using hraw
  rw [lipOmega_tel (I := I) (M := M) g gT gU]
  change covariantJetNormSq (I := I) (M := M) g 2 (X + Y) ≤ _
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (X + Y) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
          covariantJetNormSq (I := I) (M := M) g 2 Y) :=
      jet_add_lip (I := I) (M := M) g 2 X Y
    _ ≤ 2 * (C₀ * covariantJetNormSq (I := I) (M := M) g 2 AU *
          covariantJetNormSq (I := I) (M := M) g 2
            (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
              metricLoweredConnectionDifferenceCoefficient (I := I) g gU) +
        C₀ * covariantJetNormSq (I := I) (M := M) g 2 AD *
          covariantJetNormSq (I := I) (M := M) g 2
            (metricLoweredConnectionDifferenceCoefficient (I := I) g gT)) :=
      mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ = (2 * C₀) *
        (covariantJetNormSq (I := I) (M := M) g 2 AU *
            covariantJetNormSq (I := I) (M := M) g 2
              (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
                metricLoweredConnectionDifferenceCoefficient (I := I) g gU) +
          covariantJetNormSq (I := I) (M := M) g 2 AD *
            covariantJetNormSq (I := I) (M := M) g 2
              (metricLoweredConnectionDifferenceCoefficient (I := I) g gT)) := by
      ring

private theorem app_h21_mul_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        covariantJetNormSq (I := I) (M := M) g 1
            (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
          C * covariantJetNormSq (I := I) (M := M) g 2 Φ *
            covariantJetNormSq (I := I) (M := M) g 1 W := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    operator_field_composition_h2_h1_to_h1_bound (I := I) (M := M) hDim g p r c
  refine ⟨C₀ ^ 2, sq_nonneg _, ?_⟩
  intro Φ W
  let A : ℝ := Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 Φ)
  let B : ℝ := Real.sqrt (covariantJetNormSq (I := I) (M := M) g 1 W)
  have hΦ0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 Φ :=
    jet_nonneg_lip (I := I) (M := M) g Φ
  have hW0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 1 W :=
    jet_nonneg_lip (I := I) (M := M) g W
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hAsq : A ^ 2 = covariantJetNormSq (I := I) (M := M) g 2 Φ := by
    simpa only [A] using Real.sq_sqrt hΦ0
  have hBsq : B ^ 2 = covariantJetNormSq (I := I) (M := M) g 1 W := by
    simpa only [B] using Real.sq_sqrt hW0
  have hnorm := happ Φ W A B hA hB
    (by
      simpa only [covariantJetNormSq, Nat.reduceAdd] using
        (le_of_eq hAsq.symm))
    (by
      simpa only [covariantJetNormSq, Nat.reduceAdd] using
        (le_of_eq hBsq.symm))
  have hsq := pow_le_pow_left₀
    (norm_nonneg
      (⟨ccOperatorFieldComp (I := I) (M := M) g p r c Φ W⟩ :
        SmoothCcTensorH1 g p c))
    hnorm 2
  have hjet :
      covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
        (C₀ * A * B) ^ 2 := by
    rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g p c
      (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)] at hsq
    simpa only [covariantJetNormSq, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, Nat.reduceAdd,
      iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.add_zero] using hsq
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
      (C₀ * A * B) ^ 2 := hjet
    _ = C₀ ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 Φ *
        covariantJetNormSq (I := I) (M := M) g 1 W := by
      rw [mul_pow, mul_pow, hAsq, hBsq]

private theorem app_h12_mul_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        covariantJetNormSq (I := I) (M := M) g 1
            (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
          C * covariantJetNormSq (I := I) (M := M) g 1 Φ *
            covariantJetNormSq (I := I) (M := M) g 2 W := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    operator_field_composition_h1_h2_to_h1_bound (I := I) (M := M) hDim g p r c
  refine ⟨C₀ ^ 2, sq_nonneg _, ?_⟩
  intro Φ W
  let A : ℝ := Real.sqrt (covariantJetNormSq (I := I) (M := M) g 1 Φ)
  let B : ℝ := Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 W)
  have hΦ0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 1 Φ :=
    jet_nonneg_lip (I := I) (M := M) g Φ
  have hW0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 W :=
    jet_nonneg_lip (I := I) (M := M) g W
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hAsq : A ^ 2 = covariantJetNormSq (I := I) (M := M) g 1 Φ := by
    simpa only [A] using Real.sq_sqrt hΦ0
  have hBsq : B ^ 2 = covariantJetNormSq (I := I) (M := M) g 2 W := by
    simpa only [B] using Real.sq_sqrt hW0
  have hnorm := happ Φ W A B hA hB
    (by
      simpa only [covariantJetNormSq, Nat.reduceAdd] using
        (le_of_eq hAsq.symm))
    (by
      simpa only [covariantJetNormSq, Nat.reduceAdd] using
        (le_of_eq hBsq.symm))
  have hsq := pow_le_pow_left₀
    (norm_nonneg
      (⟨ccOperatorFieldComp (I := I) (M := M) g p r c Φ W⟩ :
        SmoothCcTensorH1 g p c))
    hnorm 2
  have hjet :
      covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
        (C₀ * A * B) ^ 2 := by
    rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g p c
      (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)] at hsq
    simpa only [covariantJetNormSq, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, Nat.reduceAdd,
      iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.add_zero] using hsq
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
      (C₀ * A * B) ^ 2 := hjet
    _ = C₀ ^ 2 * covariantJetNormSq (I := I) (M := M) g 1 Φ *
        covariantJetNormSq (I := I) (M := M) g 2 W := by
      rw [mul_pow, mul_pow, hAsq, hBsq]

omit [NeZero (Module.finrank ℝ E)] in
private theorem dom_h1_lip
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    covariantJetNormSq (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g σ S) =
      covariantJetNormSq (I := I) (M := M) g 1 S := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro q _
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g σ S q x

theorem riem_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) →
        (∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        covariantJetNormSq (I := I) (M := M) g 1
            (lieCorrectionZeroRiemann (I := I) (M := M) g gT -
              lieCorrectionZeroRiemann (I := I) (M := M) g gU) ≤
          (C * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖) ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hpair⟩ :=
    exists_lieCorrectionZeroRiemann_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hTHs hUHs
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (lieCorrectionZeroRiemann (I := I) (M := M) g gT -
          lieCorrectionZeroRiemann (I := I) (M := M) g gU) ≤
      covariantJetNormSq (I := I) (M := M) g 2
        (lieCorrectionZeroRiemann (I := I) (M := M) g gT -
          lieCorrectionZeroRiemann (I := I) (M := M) g gU) :=
      jet_mono_lip (I := I) (M := M) g (by norm_num) _
    _ ≤ (C * ‖ccTensorToHs (I := I) (M := M)
        g 2 (2 : ℝ) (T - U)‖) ^ 2 :=
      hpair T U gT gU hTtie hUtie hTHs hUHs

private theorem omega_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M),
        covariantJetNormSq (I := I) (M := M) g 1
            (lipOmega (I := I) (M := M) g gT -
              lipOmega (I := I) (M := M) g gU) ≤
          C *
            (covariantJetNormSq (I := I) (M := M) g 2
                (slotInsertEndoCc (I := I) (M := M) g 2
                  (metricComparisonEndomorphismField (I := I) (M := M) gU g)) *
              covariantJetNormSq (I := I) (M := M) g 1
                (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
                  metricLoweredConnectionDifferenceCoefficient (I := I) g gU) +
            covariantJetNormSq (I := I) (M := M) g 2
                (slotInsertEndoCc (I := I) (M := M) g 2
                    (metricComparisonEndomorphismField (I := I) (M := M) gT g) -
                  slotInsertEndoCc (I := I) (M := M) g 2
                    (metricComparisonEndomorphismField (I := I) (M := M) gU g)) *
              covariantJetNormSq (I := I) (M := M) g 1
                (metricLoweredConnectionDifferenceCoefficient (I := I) g gT)) := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 0 3 3
  refine ⟨2 * C₀, mul_nonneg (by norm_num) hC₀, ?_⟩
  intro gT gU
  let AU : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2
      (metricComparisonEndomorphismField (I := I) (M := M) gU g)
  let AD : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M) gT g) -
      slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M) gU g)
  let BD : SmoothCcTensor g 0 3 :=
    domDomCongrSection (I := I) g (finRotate 3)
      (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
        metricLoweredConnectionDifferenceCoefficient (I := I) g gU)
  let BT : SmoothCcTensor g 0 3 :=
    domDomCongrSection (I := I) g (finRotate 3)
      (metricLoweredConnectionDifferenceCoefficient (I := I) g gT)
  let X : SmoothCcTensor g 0 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 0 3 3 AU BD
  let Y : SmoothCcTensor g 0 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 0 3 3 AD BT
  have hX :
      covariantJetNormSq (I := I) (M := M) g 1 X ≤
        C₀ * covariantJetNormSq (I := I) (M := M) g 2 AU *
          covariantJetNormSq (I := I) (M := M) g 1
            (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
              metricLoweredConnectionDifferenceCoefficient (I := I) g gU) := by
    have hraw := happ AU BD
    rw [dom_h1_lip] at hraw
    simpa only [X, BD] using hraw
  have hY :
      covariantJetNormSq (I := I) (M := M) g 1 Y ≤
        C₀ * covariantJetNormSq (I := I) (M := M) g 2 AD *
          covariantJetNormSq (I := I) (M := M) g 1
            (metricLoweredConnectionDifferenceCoefficient (I := I) g gT) := by
    have hraw := happ AD BT
    rw [dom_h1_lip] at hraw
    simpa only [Y, BT] using hraw
  rw [lipOmega_tel (I := I) (M := M) g gT gU]
  change covariantJetNormSq (I := I) (M := M) g 1 (X + Y) ≤ _
  calc
    covariantJetNormSq (I := I) (M := M) g 1 (X + Y) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 1 X +
          covariantJetNormSq (I := I) (M := M) g 1 Y) :=
      jet_add_lip (I := I) (M := M) g 1 X Y
    _ ≤ 2 * (C₀ * covariantJetNormSq (I := I) (M := M) g 2 AU *
          covariantJetNormSq (I := I) (M := M) g 1
            (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
              metricLoweredConnectionDifferenceCoefficient (I := I) g gU) +
        C₀ * covariantJetNormSq (I := I) (M := M) g 2 AD *
          covariantJetNormSq (I := I) (M := M) g 1
            (metricLoweredConnectionDifferenceCoefficient (I := I) g gT)) :=
      mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ = (2 * C₀) *
        (covariantJetNormSq (I := I) (M := M) g 2 AU *
            covariantJetNormSq (I := I) (M := M) g 1
              (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
                metricLoweredConnectionDifferenceCoefficient (I := I) g gU) +
          covariantJetNormSq (I := I) (M := M) g 2 AD *
            covariantJetNormSq (I := I) (M := M) g 1
              (metricLoweredConnectionDifferenceCoefficient (I := I) g gT)) := by
      ring

theorem lieOmega_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 1
          (lipOmega (I := I) (M := M) g gT -
            lipOmega (I := I) (M := M) g gU) ≤
        (B0 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨C, hC, hpair⟩ :=
    omega_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨Cr, hCr, hrevB⟩ :=
    RicciDeTurckLowOrder.reverse_slot_sobolev_two_bound (I := I) (M := M) g
  obtain ⟨Bs, hBs, hwSelf⟩ :=
    wXi_self_tame (I := I) (M := M) hDim g
  obtain ⟨W0, W1, hW0, hW1, hwDiff⟩ :=
    exists_metricLoweredConnectionDifference_covariantJetNormSq_one_sub_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let Hc : ℝ := Real.sqrt C
  let fr : ℝ := Module.finrank ℝ E
  let B0 : ℝ → ℝ := fun R =>
    Hc * (Cr * (1 + R)) * W0 R
  let B1 : ℝ → ℝ := fun R =>
    Hc * (Cr * (1 + R) * W1 R + fr * Bs R)
  have hHc : 0 ≤ Hc := Real.sqrt_nonneg _
  have hHcSq : Hc ^ 2 = C := by
    simpa only [Hc] using Real.sq_sqrt hC
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨B0, B1, ?_, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg
      (mul_nonneg hHc (mul_nonneg hCr (by linarith)))
      (hW0 R hR)
  · intro R hR
    exact mul_nonneg hHc
      (add_nonneg
        (mul_nonneg (mul_nonneg hCr (by linarith)) (hW1 R hR))
        (mul_nonneg hfr (hBs R hR)))
  intro gT gU T U hT hU hTtie hUtie
    δ hδ_le hδ0 hδT hδU hδZ
    R A D2 hR hA hD2 hT2 hU2 hT3 hTU2
  let AU : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (slotInsertEndoCc (I := I) (M := M) g 2
      (metricComparisonEndomorphismField (I := I) (M := M) gU g))
  let AD : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M) gT g) -
      slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M) gU g))
  let WT : ℝ := covariantJetNormSq (I := I) (M := M) g 1
    (metricLoweredConnectionDifference (I := I) (M := M) g gT g)
  let WD : ℝ := covariantJetNormSq (I := I) (M := M) g 1
    (metricLoweredConnectionDifference (I := I) (M := M) g gT g -
      metricLoweredConnectionDifference (I := I) (M := M) g gU g)
  let X : ℝ := W0 R * D2 + W1 R * A * D2
  let P : ℝ := Cr * (1 + R)
  let Q : ℝ := fr * Bs R
  let L : ℝ := Hc * (P * X + Q * A * D2)
  have hAU0 : 0 ≤ AU := jet_nonneg_lip (I := I) (M := M) g _
  have hAD0 : 0 ≤ AD := jet_nonneg_lip (I := I) (M := M) g _
  have hWT0 : 0 ≤ WT := jet_nonneg_lip (I := I) (M := M) g _
  have hWD0 : 0 ≤ WD := jet_nonneg_lip (I := I) (M := M) g _
  have hW0R : 0 ≤ W0 R := hW0 R hR
  have hW1R : 0 ≤ W1 R := hW1 R hR
  have hBsR : 0 ≤ Bs R := hBs R hR
  have hP : 0 ≤ P := mul_nonneg hCr (by linarith)
  have hQ : 0 ≤ Q := mul_nonneg hfr hBsR
  have hX : 0 ≤ X :=
    add_nonneg (mul_nonneg hW0R hD2)
      (mul_nonneg (mul_nonneg hW1R hA) hD2)
  have hAU :
      AU ≤ P ^ 2 := by
    simpa only [AU, P] using
      hrevB gU U hU hUtie R hR hU2
  have hAD :
      AD ≤ (fr * D2) ^ 2 := by
    have hraw :=
      RicciDeTurckLowOrder.revSlot_pair_h2 (I := I) (M := M)
        g gT gU T U hT hU hTtie hUtie
    calc
      AD ≤ fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 (T - U) := by
        simpa only [AD, fr] using hraw
      _ ≤ fr ^ 2 * D2 ^ 2 :=
        mul_le_mul_of_nonneg_left hTU2 (sq_nonneg fr)
      _ = (fr * D2) ^ 2 := by ring
  have hWT :
      WT ≤ (Bs R * A) ^ 2 := by
    calc
      WT ≤ covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g) :=
        jet_mono_lip (I := I) (M := M) g (by norm_num) _
      _ ≤ (Bs R * A) ^ 2 :=
        hwSelf gT T hT hTtie hδ_le hδ0 hδT hδZ
          R A hR hA hT2 hT3
  have hWD :
      WD ≤ X ^ 2 := by
    simpa only [WD, X] using
      hwDiff gT gU g T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R A D2 hR hA hD2 hU2 hT3 hTU2
  have hPairRaw :
      covariantJetNormSq (I := I) (M := M) g 1
          (lipOmega (I := I) (M := M) g gT -
            lipOmega (I := I) (M := M) g gU) ≤
        C * (AU * WD + AD * WT) := by
    simpa only [AU, AD, WT, WD, metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc] using hpair gT gU
  have hFirst : AU * WD ≤ (P * X) ^ 2 := by
    calc
      AU * WD ≤ P ^ 2 * X ^ 2 :=
        mul_le_mul hAU hWD hWD0 (sq_nonneg P)
      _ = (P * X) ^ 2 := by ring
  have hSecond : AD * WT ≤ (Q * A * D2) ^ 2 := by
    calc
      AD * WT ≤ (fr * D2) ^ 2 * (Bs R * A) ^ 2 :=
        mul_le_mul hAD hWT hWT0 (sq_nonneg (fr * D2))
      _ = (Q * A * D2) ^ 2 := by
        simp only [Q]
        ring
  have hPX : 0 ≤ P * X := mul_nonneg hP hX
  have hQAD : 0 ≤ Q * A * D2 :=
    mul_nonneg (mul_nonneg hQ hA) hD2
  have hToL :
      C * (AU * WD + AD * WT) ≤ L ^ 2 := by
    calc
      C * (AU * WD + AD * WT) ≤
          C * ((P * X) ^ 2 + (Q * A * D2) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond) hC
      _ ≤ C * (P * X + Q * A * D2) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hC
        nlinarith only [mul_nonneg hPX hQAD]
      _ = L ^ 2 := by
        simp only [L]
        rw [mul_pow, hHcSq]
  have hLeq : L = B0 R * D2 + B1 R * A * D2 := by
    simp only [L, B0, B1, P, Q, X]
    ring
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (lipOmega (I := I) (M := M) g gT -
          lipOmega (I := I) (M := M) g gU) ≤
      C * (AU * WD + AD * WT) := hPairRaw
    _ ≤ L ^ 2 := hToL
    _ = (B0 R * D2 + B1 R * A * D2) ^ 2 := by rw [hLeq]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem hat_eq_lip
    (g gm : SmoothRiemannianMetric I M) :
    connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gm =
      lipOmega (I := I) (M := M) g gm := rfl

private theorem curvF_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2),
        covariantJetNormSq (I := I) (M := M) g 1
            (riemannCurvatureCoefficientField (I := I) (M := M) g T -
              riemannCurvatureCoefficientField (I := I) (M := M) g U) ≤
          C * covariantJetNormSq (I := I) (M := M) g 2 (T - U) := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 0 2 4
  let J1w : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (riemannLoweredContractionA (I := I) (M := M) g)
  let J2w : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (riemannLoweredContractionB (I := I) (M := M) g)
  have hJ1w : 0 ≤ J1w := jet_nonneg_lip (I := I) (M := M) g _
  have hJ2w : 0 ≤ J2w := jet_nonneg_lip (I := I) (M := M) g _
  refine ⟨2 * (C₀ * J1w + C₀ * J2w),
    mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg hC₀ hJ1w) (mul_nonneg hC₀ hJ2w)), ?_⟩
  intro T U
  have hsub :
      riemannCurvatureCoefficientField (I := I) (M := M) g T -
          riemannCurvatureCoefficientField (I := I) (M := M) g U =
        ccOperatorFieldComp (I := I) (M := M) g 0 2 4
            (riemannLoweredContractionA (I := I) (M := M) g) (T - U) +
          ccOperatorFieldComp (I := I) (M := M) g 0 2 4
            (riemannLoweredContractionB (I := I) (M := M) g) (T - U) := by
    simp only [riemannCurvatureCoefficientField, riemannCurvatureCoefficientField]
    rw [operatorFieldComposition_sub_right, operatorFieldComposition_sub_right]
    module
  have hX := happ (riemannLoweredContractionA (I := I) (M := M) g) (T - U)
  have hY := happ (riemannLoweredContractionB (I := I) (M := M) g) (T - U)
  have hmono :
      covariantJetNormSq (I := I) (M := M) g 1 (T - U) ≤
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) :=
    jet_mono_lip (I := I) (M := M) g (by norm_num) _
  have hTU0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 (T - U) :=
    jet_nonneg_lip (I := I) (M := M) g _
  rw [hsub]
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (ccOperatorFieldComp (I := I) (M := M) g 0 2 4
            (riemannLoweredContractionA (I := I) (M := M) g) (T - U) +
          ccOperatorFieldComp (I := I) (M := M) g 0 2 4
            (riemannLoweredContractionB (I := I) (M := M) g) (T - U)) ≤
      2 * (covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g 0 2 4
            (riemannLoweredContractionA (I := I) (M := M) g) (T - U)) +
        covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g 0 2 4
            (riemannLoweredContractionB (I := I) (M := M) g) (T - U))) :=
      jet_add_lip (I := I) (M := M) g 1 _ _
    _ ≤ 2 * (C₀ * J1w *
          covariantJetNormSq (I := I) (M := M) g 1 (T - U) +
        C₀ * J2w *
          covariantJetNormSq (I := I) (M := M) g 1 (T - U)) := by
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
      · simpa only [J1w] using hX
      · simpa only [J2w] using hY
    _ ≤ 2 * (C₀ * J1w *
          covariantJetNormSq (I := I) (M := M) g 2 (T - U) +
        C₀ * J2w *
          covariantJetNormSq (I := I) (M := M) g 2 (T - U)) := by
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
      · exact mul_le_mul_of_nonneg_left hmono
          (mul_nonneg hC₀ hJ1w)
      · exact mul_le_mul_of_nonneg_left hmono
          (mul_nonneg hC₀ hJ2w)
    _ = 2 * (C₀ * J1w + C₀ * J2w) *
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) := by ring

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem quadB_tel
    (g gT gU : SmoothRiemannianMetric I M) :
    connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gT -
        connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gU =
      ccOperatorFieldComp (I := I) (M := M) g 0 3 4
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
          (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
            connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU) +
        ccOperatorFieldComp (I := I) (M := M) g 0 3 4
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
            bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
          (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT) := by
  simp only [connectionDifferenceQuadraticPairedTensor, connectionDifferenceQuadraticPairedTensor, connectionDifferenceEndomorphism]
  rw [operatorFieldComposition_sub_right, operatorFieldComposition_sub_left]
  module

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem quadA_tel
    (g gT gU : SmoothRiemannianMetric I M) :
    connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT -
        connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gU =
      ccOperatorFieldComp (I := I) (M := M) g 0 3 4
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1)
            (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
              connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU)) +
        ccOperatorFieldComp (I := I) (M := M) g 0 3 4
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
            bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1)
            (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT)) := by
  simp only [connectionDifferenceQuadraticComposedTensor, connectionDifferenceQuadraticComposedTensor, connectionDifferenceEndomorphism]
  rw [dom_sub_lip, operatorFieldComposition_sub_right, operatorFieldComposition_sub_left]
  module

private theorem weighted_two_term_le_weight_sum
    {C₀ C₁ X Y : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    C₀ * X + C₁ * Y ≤ (C₀ + C₁) * (X + Y) := by
  nlinarith only [mul_nonneg hC₀ hY, mul_nonneg hC₁ hX]

private theorem quad_pair_scalar
    {C₀ C₁ S x y : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hS : 0 ≤ S) (hx : x ≤ 2 * (C₀ + C₁) * S)
    (hy : y ≤ 2 * (C₀ + C₁) * S) :
    2 * x + 2 * (2 * x +
      2 * (2 * y + 2 * (2 * y + 2 * (2 * (y + y))))) ≤
      384 * (C₀ + C₁) * S := by
  nlinarith only [hx, hy, mul_nonneg (add_nonneg hC₀ hC₁) hS]

private theorem sq_add_sq_le_sum_sq
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ 2 + y ^ 2 ≤ (x + y) ^ 2 := by
  nlinarith only [mul_nonneg hx hy]

private theorem quad_nested_le
    {K x y : ℝ} (hK : 0 ≤ K) (hx : x ≤ K) (hy : y ≤ K) :
    2 * x + 2 * (2 * x +
      2 * (2 * y + 2 * (2 * y + 2 * (2 * (y + y))))) ≤
      384 * K := by
  nlinarith only [hK, hx, hy]

private theorem sq_mul_sq_le_add_sq_sq {A : ℝ} (hA : 0 ≤ A) :
    A ^ 2 * A ^ 2 ≤ (A + A ^ 2) ^ 2 := by
  nlinarith only [sq_nonneg A, mul_nonneg hA (sq_nonneg A)]

private theorem unit_interval_sq_le_one_lip
    {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : s ^ 2 ≤ (1 : ℝ) := by
  nlinarith only [h0, h1]

private theorem half_sq_le_one_lip
    {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : (s / 2) ^ 2 ≤ (1 : ℝ) := by
  nlinarith only [h0, h1]

private theorem sq_le_add_sq_sq {A : ℝ} (hA : 0 ≤ A) :
    A ^ 2 ≤ (A + A ^ 2) ^ 2 := by
  nlinarith only [sq_nonneg A, mul_nonneg hA (sq_nonneg A)]

private theorem sq_le_one_add_add_sq_sq {A : ℝ} (hA : 0 ≤ A) :
    A ^ 2 ≤ (1 + A + A ^ 2) ^ 2 := by
  nlinarith only [hA, sq_nonneg A, mul_nonneg hA (sq_nonneg A)]

private theorem add_sq_le_one_add_add_sq_sq {A : ℝ} (hA : 0 ≤ A) :
    A + A ^ 2 ≤ (1 + A + A ^ 2) ^ 2 := by
  nlinarith only [hA, sq_nonneg A, mul_nonneg hA (sq_nonneg A)]

private theorem add_sq_le_two_sq (x y : ℝ) :
    (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith only [sq_nonneg (x - y)]

private theorem affine_pair_sq_le_weight_lip
    (b0 b1 A D pl u : ℝ)
    (hD : D ^ 2 ≤ pl * u) (hAD : A ^ 2 * D ^ 2 ≤ pl * u) :
    (b0 * D + b1 * A * D) ^ 2 ≤
      (2 * b0 ^ 2 + 2 * b1 ^ 2) * (pl * u) := by
  calc
    (b0 * D + b1 * A * D) ^ 2 ≤
        2 * (b0 * D) ^ 2 + 2 * (b1 * A * D) ^ 2 :=
      add_sq_le_two_sq _ _
    _ = 2 * b0 ^ 2 * D ^ 2 + 2 * b1 ^ 2 * (A ^ 2 * D ^ 2) := by ring
    _ ≤ 2 * b0 ^ 2 * (pl * u) + 2 * b1 ^ 2 * (pl * u) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hD (by positivity))
        (mul_le_mul_of_nonneg_left hAD (by positivity))
    _ = (2 * b0 ^ 2 + 2 * b1 ^ 2) * (pl * u) := by ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem jet_add_bound_step_lip
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (X Y : SmoothCcTensor g 2 4) (a q : ℝ)
    (hX : covariantJetNormSq (I := I) (M := M) g m X ≤ a * q)
    (hY : covariantJetNormSq (I := I) (M := M) g m Y ≤ q) :
    covariantJetNormSq (I := I) (M := M) g m (X + Y) ≤ (2 * a + 2) * q := by
  calc
    covariantJetNormSq (I := I) (M := M) g m (X + Y) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g m X +
          covariantJetNormSq (I := I) (M := M) g m Y) :=
      jet_add_lip (I := I) (M := M) g m X Y
    _ ≤ 2 * (a * q + q) :=
      mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ = (2 * a + 2) * q := by ring

private theorem quad_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M),
        covariantJetNormSq (I := I) (M := M) g 1
            (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gT -
              connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gU) ≤
          C *
            (covariantJetNormSq (I := I) (M := M) g 2
                (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                  (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) *
              covariantJetNormSq (I := I) (M := M) g 1
                (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
                  connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU) +
            covariantJetNormSq (I := I) (M := M) g 1
                (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                    (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
                  bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                    (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) *
              covariantJetNormSq (I := I) (M := M) g 2
                (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT)) := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 0 3 4
  obtain ⟨C₁, hC₁, happ12⟩ :=
    app_h12_mul_lip (I := I) (M := M) hDim g 0 3 4
  refine ⟨384 * (C₀ + C₁), by positivity, ?_⟩
  intro gT gU
  set cU : SmoothCcTensor g 3 4 :=
    bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
      (connectionDifferenceEndomorphism (I := I) (M := M) g gU) with hcU
  set cD : SmoothCcTensor g 3 4 :=
    bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
        (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
      bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
        (connectionDifferenceEndomorphism (I := I) (M := M) g gU) with hcD
  set hatT : SmoothCcTensor g 0 3 :=
    connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT with hhatT
  set hatD : SmoothCcTensor g 0 3 :=
    connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
      connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU with hhatD
  set S : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2 cU *
        covariantJetNormSq (I := I) (M := M) g 1 hatD +
      covariantJetNormSq (I := I) (M := M) g 1 cD *
        covariantJetNormSq (I := I) (M := M) g 2 hatT with hSdef
  have hS0 : 0 ≤ S :=
    add_nonneg
      (mul_nonneg (jet_nonneg_lip (I := I) (M := M) g _)
        (jet_nonneg_lip (I := I) (M := M) g _))
      (mul_nonneg (jet_nonneg_lip (I := I) (M := M) g _)
        (jet_nonneg_lip (I := I) (M := M) g _))
  set QBd : SmoothCcTensor g 0 4 :=
    connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gU with hQBd
  set QAd : SmoothCcTensor g 0 4 :=
    connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gU with hQAd
  have htelB : QBd =
      ccOperatorFieldComp (I := I) (M := M) g 0 3 4 cU hatD +
        ccOperatorFieldComp (I := I) (M := M) g 0 3 4 cD hatT := by
    rw [hQBd, hcU, hcD, hhatT, hhatD]
    exact quadB_tel (I := I) (M := M) g gT gU
  have htelA : QAd =
      ccOperatorFieldComp (I := I) (M := M) g 0 3 4 cU
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 3) 1) hatD) +
        ccOperatorFieldComp (I := I) (M := M) g 0 3 4 cD
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 3) 1) hatT) := by
    rw [hQAd, hcU, hcD, hhatT, hhatD]
    exact quadA_tel (I := I) (M := M) g gT gU
  set x : ℝ := covariantJetNormSq (I := I) (M := M) g 1 QBd with hxdef
  set y : ℝ := covariantJetNormSq (I := I) (M := M) g 1 QAd with hydef
  have hQB : x ≤ 2 * (C₀ + C₁) * S := by
    rw [hxdef]
    have hX := happ cU hatD
    have hY := happ12 cD hatT
    calc
      covariantJetNormSq (I := I) (M := M) g 1 QBd =
          covariantJetNormSq (I := I) (M := M) g 1
            (ccOperatorFieldComp (I := I) (M := M) g 0 3 4 cU hatD +
              ccOperatorFieldComp (I := I) (M := M) g 0 3 4 cD hatT) := by
        rw [htelB]
      _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 1
            (ccOperatorFieldComp (I := I) (M := M) g 0 3 4 cU hatD) +
          covariantJetNormSq (I := I) (M := M) g 1
            (ccOperatorFieldComp (I := I) (M := M) g 0 3 4 cD hatT)) :=
        jet_add_lip (I := I) (M := M) g 1 _ _
      _ ≤ 2 * (C₀ * covariantJetNormSq (I := I) (M := M) g 2 cU *
            covariantJetNormSq (I := I) (M := M) g 1 hatD +
          C₁ * covariantJetNormSq (I := I) (M := M) g 1 cD *
            covariantJetNormSq (I := I) (M := M) g 2 hatT) :=
        mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
      _ ≤ 2 * (C₀ + C₁) * S := by
        rw [hSdef]
        have h := mul_le_mul_of_nonneg_left
          (weighted_two_term_le_weight_sum hC₀ hC₁
            (mul_nonneg
              (jet_nonneg_lip (I := I) (M := M) g (m := 2) cU)
              (jet_nonneg_lip (I := I) (M := M) g (m := 1) hatD))
            (mul_nonneg
              (jet_nonneg_lip (I := I) (M := M) g (m := 1) cD)
              (jet_nonneg_lip (I := I) (M := M) g (m := 2) hatT)))
          (show 0 ≤ (2 : ℝ) by norm_num)
        simpa only [mul_assoc] using h
  have hQA : y ≤ 2 * (C₀ + C₁) * S := by
    rw [hydef]
    have hX := happ cU
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1) hatD)
    have hY := happ12 cD
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1) hatT)
    rw [dom_h1_lip] at hX
    rw [dom_h2_lip] at hY
    calc
      covariantJetNormSq (I := I) (M := M) g 1 QAd =
          covariantJetNormSq (I := I) (M := M) g 1
            (ccOperatorFieldComp (I := I) (M := M) g 0 3 4 cU
                (domDomCongrSection (I := I) g
                  (Equiv.swap (0 : Fin 3) 1) hatD) +
              ccOperatorFieldComp (I := I) (M := M) g 0 3 4 cD
                (domDomCongrSection (I := I) g
                  (Equiv.swap (0 : Fin 3) 1) hatT)) := by
        rw [htelA]
      _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 1
            (ccOperatorFieldComp (I := I) (M := M) g 0 3 4 cU
              (domDomCongrSection (I := I) g
                (Equiv.swap (0 : Fin 3) 1) hatD)) +
          covariantJetNormSq (I := I) (M := M) g 1
            (ccOperatorFieldComp (I := I) (M := M) g 0 3 4 cD
              (domDomCongrSection (I := I) g
                (Equiv.swap (0 : Fin 3) 1) hatT))) :=
        jet_add_lip (I := I) (M := M) g 1 _ _
      _ ≤ 2 * (C₀ * covariantJetNormSq (I := I) (M := M) g 2 cU *
            covariantJetNormSq (I := I) (M := M) g 1 hatD +
          C₁ * covariantJetNormSq (I := I) (M := M) g 1 cD *
            covariantJetNormSq (I := I) (M := M) g 2 hatT) :=
        mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
      _ ≤ 2 * (C₀ + C₁) * S := by
        rw [hSdef]
        have h := mul_le_mul_of_nonneg_left
          (weighted_two_term_le_weight_sum hC₀ hC₁
            (mul_nonneg
              (jet_nonneg_lip (I := I) (M := M) g (m := 2) cU)
              (jet_nonneg_lip (I := I) (M := M) g (m := 1) hatD))
            (mul_nonneg
              (jet_nonneg_lip (I := I) (M := M) g (m := 1) cD)
              (jet_nonneg_lip (I := I) (M := M) g (m := 2) hatT)))
          (show 0 ≤ (2 : ℝ) by norm_num)
        simpa only [mul_assoc] using h
  have hsplit :
      connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gT -
          connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gU =
        domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) QBd +
          (QBd +
            (domDomCongrSection (I := I) g lrPermA QAd +
              (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd +
                (domDomCongrSection (I := I) g lrPermB QAd +
                  domDomCongrSection (I := I) g lrPermC QAd)))) := by
    rw [hQBd, hQAd]
    simp only [connectionDifferenceQuadraticCurvatureTerm, connectionDifferenceQuadraticCurvatureTerm, connectionDifferenceQuadraticPairedTensor,
      connectionDifferenceQuadraticPairedTensor, connectionDifferenceQuadraticComposedTensor, connectionDifferenceQuadraticComposedTensor,
      dom_sub_lip]
    abel
  have hd1 : covariantJetNormSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) QBd) =
      covariantJetNormSq (I := I) (M := M) g 1 QBd :=
    dom_h1_lip (I := I) (M := M) g _ _
  have hd3 : covariantJetNormSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermA QAd) =
      covariantJetNormSq (I := I) (M := M) g 1 QAd :=
    dom_h1_lip (I := I) (M := M) g _ _
  have hd4 : covariantJetNormSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd) =
      covariantJetNormSq (I := I) (M := M) g 1 QAd :=
    dom_h1_lip (I := I) (M := M) g _ _
  have hd5 : covariantJetNormSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermB QAd) =
      covariantJetNormSq (I := I) (M := M) g 1 QAd :=
    dom_h1_lip (I := I) (M := M) g _ _
  have hd6 : covariantJetNormSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermC QAd) =
      covariantJetNormSq (I := I) (M := M) g 1 QAd :=
    dom_h1_lip (I := I) (M := M) g _ _
  have hQB0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 1 QBd :=
    jet_nonneg_lip (I := I) (M := M) g _
  have hQA0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 1 QAd :=
    jet_nonneg_lip (I := I) (M := M) g _
  have h56 : covariantJetNormSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermB QAd +
        domDomCongrSection (I := I) g lrPermC QAd) ≤
      2 * (covariantJetNormSq (I := I) (M := M) g 1 QAd +
        covariantJetNormSq (I := I) (M := M) g 1 QAd) := by
    linarith [jet_add_lip (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g lrPermB QAd)
        (domDomCongrSection (I := I) g lrPermC QAd),
      hd5, hd6]
  have h456 : covariantJetNormSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd +
        (domDomCongrSection (I := I) g lrPermB QAd +
          domDomCongrSection (I := I) g lrPermC QAd)) ≤
      2 * covariantJetNormSq (I := I) (M := M) g 1 QAd +
        2 * (2 * (covariantJetNormSq (I := I) (M := M) g 1 QAd +
          covariantJetNormSq (I := I) (M := M) g 1 QAd)) := by
    linarith [jet_add_lip (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd)
        (domDomCongrSection (I := I) g lrPermB QAd +
          domDomCongrSection (I := I) g lrPermC QAd),
      hd4, h56]
  have h3456 : covariantJetNormSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermA QAd +
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd +
          (domDomCongrSection (I := I) g lrPermB QAd +
            domDomCongrSection (I := I) g lrPermC QAd))) ≤
      2 * covariantJetNormSq (I := I) (M := M) g 1 QAd +
        2 * (2 * covariantJetNormSq (I := I) (M := M) g 1 QAd +
          2 * (2 * (covariantJetNormSq (I := I) (M := M) g 1 QAd +
            covariantJetNormSq (I := I) (M := M) g 1 QAd))) := by
    linarith [jet_add_lip (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g lrPermA QAd)
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd +
          (domDomCongrSection (I := I) g lrPermB QAd +
            domDomCongrSection (I := I) g lrPermC QAd)),
      hd3, h456]
  have h23456 : covariantJetNormSq (I := I) (M := M) g 1
      (QBd +
        (domDomCongrSection (I := I) g lrPermA QAd +
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd +
            (domDomCongrSection (I := I) g lrPermB QAd +
              domDomCongrSection (I := I) g lrPermC QAd)))) ≤
      2 * covariantJetNormSq (I := I) (M := M) g 1 QBd +
        2 * (2 * covariantJetNormSq (I := I) (M := M) g 1 QAd +
          2 * (2 * covariantJetNormSq (I := I) (M := M) g 1 QAd +
            2 * (2 * (covariantJetNormSq (I := I) (M := M) g 1 QAd +
              covariantJetNormSq (I := I) (M := M) g 1 QAd)))) := by
    linarith [jet_add_lip (I := I) (M := M) g 1 QBd
        (domDomCongrSection (I := I) g lrPermA QAd +
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd +
            (domDomCongrSection (I := I) g lrPermB QAd +
              domDomCongrSection (I := I) g lrPermC QAd))),
      h3456]
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gT -
          connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gU) =
      covariantJetNormSq (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) QBd +
          (QBd +
            (domDomCongrSection (I := I) g lrPermA QAd +
              (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd +
                (domDomCongrSection (I := I) g lrPermB QAd +
                  domDomCongrSection (I := I) g lrPermC QAd))))) := by
      rw [hsplit]
    _ ≤ 2 * covariantJetNormSq (I := I) (M := M) g 1 QBd +
        2 * (2 * covariantJetNormSq (I := I) (M := M) g 1 QBd +
          2 * (2 * covariantJetNormSq (I := I) (M := M) g 1 QAd +
            2 * (2 * covariantJetNormSq (I := I) (M := M) g 1 QAd +
              2 * (2 * (covariantJetNormSq (I := I) (M := M) g 1 QAd +
                covariantJetNormSq (I := I) (M := M) g 1 QAd))))) := by
      linarith [jet_add_lip (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) QBd)
          (QBd +
            (domDomCongrSection (I := I) g lrPermA QAd +
              (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd +
                (domDomCongrSection (I := I) g lrPermB QAd +
                  domDomCongrSection (I := I) g lrPermC QAd)))),
        hd1, h23456]
    _ = 2 * x +
        2 * (2 * x +
          2 * (2 * y +
            2 * (2 * y +
              2 * (2 * (y + y))))) := by
      rw [hxdef, hydef]
    _ ≤ 384 * (C₀ + C₁) * S :=
      quad_pair_scalar hC₀ hC₁ hS0 hQB hQA

private theorem r4_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2) {δ : ℝ}
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
        covariantJetNormSq (I := I) (M := M) g 1
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
              deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s) ≤
          C *
            (covariantJetNormSq (I := I) (M := M) g 2 (T - U) +
              (covariantJetNormSq (I := I) (M := M) g 2
                  (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                    (connectionDifferenceEndomorphism (I := I) (M := M) g
                      (metricPerturbationPath (I := I) g U 0 hδU hδZ s))) *
                covariantJetNormSq (I := I) (M := M) g 1
                  (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g
                      (metricPerturbationPath (I := I) g T 0 hδT hδZ s) -
                    connectionDifferenceMetricLoweredTensor (I := I) (M := M) g
                      (metricPerturbationPath (I := I) g U 0 hδU hδZ s)) +
              covariantJetNormSq (I := I) (M := M) g 1
                  (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                      (connectionDifferenceEndomorphism (I := I) (M := M) g
                        (metricPerturbationPath (I := I) g T 0 hδT hδZ s)) -
                    bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                      (connectionDifferenceEndomorphism (I := I) (M := M) g
                        (metricPerturbationPath (I := I) g U 0 hδU hδZ s))) *
                covariantJetNormSq (I := I) (M := M) g 2
                  (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g
                    (metricPerturbationPath (I := I) g T 0 hδT hδZ s)))) := by
  obtain ⟨Cc, hCc, hcurv⟩ :=
    curvF_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨Cq, hCq, hquad⟩ :=
    quad_pair_h1 (I := I) (M := M) hDim g
  refine ⟨2 * Cc + 2 * Cq, by positivity, ?_⟩
  intro T U δ hδT hδU hδZ s hs
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU
  set CFd : SmoothCcTensor g 0 4 :=
    riemannCurvatureCoefficientField (I := I) (M := M) g T -
      riemannCurvatureCoefficientField (I := I) (M := M) g U with hCFd
  set QFd : SmoothCcTensor g 0 4 :=
    connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmT -
      connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmU with hQFd
  have hdecomp :
      deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
          deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s =
        (-(s / 2) : ℝ) • CFd + (-1 : ℝ) • QFd := by
    rw [hCFd, hQFd, hgmT, hgmU,
      deTurckLieCovariantDerivativeRemainderTensor_eq (I := I) (M := M) g T hδT hδZ s,
      deTurckLieCovariantDerivativeRemainderTensor_eq (I := I) (M := M) g U hδU hδZ s]
    module
  set a : ℝ := covariantJetNormSq (I := I) (M := M) g 2 (T - U) with ha
  set b : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gmU)) *
      covariantJetNormSq (I := I) (M := M) g 1
        (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmT -
          connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmU) +
    covariantJetNormSq (I := I) (M := M) g 1
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gmT) -
          bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gmU)) *
      covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmT) with hb
  have ha0 : 0 ≤ a := jet_nonneg_lip (I := I) (M := M) g _
  have hb0 : 0 ≤ b :=
    add_nonneg
      (mul_nonneg (jet_nonneg_lip (I := I) (M := M) g _)
        (jet_nonneg_lip (I := I) (M := M) g _))
      (mul_nonneg (jet_nonneg_lip (I := I) (M := M) g _)
        (jet_nonneg_lip (I := I) (M := M) g _))
  have hCF : covariantJetNormSq (I := I) (M := M) g 1 CFd ≤ Cc * a := by
    rw [hCFd, ha]
    exact hcurv T U
  have hQF : covariantJetNormSq (I := I) (M := M) g 1 QFd ≤ Cq * b := by
    rw [hQFd, hb]
    exact hquad gmT gmU
  have hs2 : (s / 2) ^ 2 ≤ 1 := by
    obtain ⟨hs0, hs1⟩ := hs
    exact half_sq_le_one_lip hs0 hs1
  set u : ℝ := covariantJetNormSq (I := I) (M := M) g 1 CFd with hu
  set v : ℝ := covariantJetNormSq (I := I) (M := M) g 1 QFd with hv
  have hu0 : 0 ≤ u := jet_nonneg_lip (I := I) (M := M) g _
  have hv0 : 0 ≤ v := jet_nonneg_lip (I := I) (M := M) g _
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
          deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s) =
      covariantJetNormSq (I := I) (M := M) g 1
        ((-(s / 2) : ℝ) • CFd + (-1 : ℝ) • QFd) := by
      rw [hdecomp]
    _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 1
          ((-(s / 2) : ℝ) • CFd) +
        covariantJetNormSq (I := I) (M := M) g 1
          ((-1 : ℝ) • QFd)) :=
      jet_add_lip (I := I) (M := M) g 1 _ _
    _ = 2 * ((-(s / 2)) ^ 2 * u + (-1 : ℝ) ^ 2 * v) := by
      rw [jet_smul_lip, jet_smul_lip, hu, hv]
    _ ≤ 2 * (Cc * a + Cq * b) := by
      have h1 : (-(s / 2)) ^ 2 * u ≤ Cc * a := by
        have hle : (-(s / 2)) ^ 2 * u ≤ 1 * u := by
          have : (-(s / 2)) ^ 2 = (s / 2) ^ 2 := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_right hs2 hu0
        rw [one_mul] at hle
        exact hle.trans (by rw [hu]; exact hCF)
      have h2 : (-1 : ℝ) ^ 2 * v ≤ Cq * b := by
        have : ((-1 : ℝ) ^ 2 * v) = v := by ring
        rw [this, hv]
        exact hQF
      linarith
    _ ≤ (2 * Cc + 2 * Cq) * (a + b) := by nlinarith only [hCc, hCq, ha0, hb0]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem lcvPair_eq_lip
    (g gm : SmoothRiemannianMetric I M) :
    cometricDoublePairTraceCoefficient (I := I) (M := M) g gm =
      ccOperatorFieldComp (I := I) (M := M) g 6 4 2
        (pureTrace (I := I) (M := M) g gm 2)
        (pureTrace (I := I) (M := M) g gm 4) := rfl

private theorem lcvPair_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        covariantJetNormSq (I := I) (M := M) g 2
            (cometricDoublePairTraceCoefficient (I := I) (M := M) g gT -
              cometricDoublePairTraceCoefficient (I := I) (M := M) g gU) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ₂, C₂, hρ₂, hC₂, hp₂⟩ :=
    RicciDeTurckLowOrder.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρ₄, C₄, hρ₄, hC₄, hp₄⟩ :=
    RicciDeTurckLowOrder.trace4_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb₂, B₂, hρb₂, hB₂, hb₂⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρb₄, B₄, hρb₄, hB₄, hb₄⟩ :=
    RicciDeTurckLowOrder.trace_four_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul_lip (I := I) (M := M) hDim g 6 4 2
  refine ⟨min (min ρ₂ ρ₄) (min ρb₂ ρb₄),
    Real.sqrt (2 * (Ca * B₂ ^ 2 * C₄ ^ 2 + Ca * C₂ ^ 2 * B₄ ^ 2)),
    lt_min (lt_min hρ₂ hρ₄) (lt_min hρb₂ hρb₄),
    Real.sqrt_nonneg _, ?_⟩
  intro T U gT gU hTtie hUtie hTn hUn
  have hT₂ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ₂ :=
    hTn.trans (le_trans (min_le_left _ _) (min_le_left _ _))
  have hU₂ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ₂ :=
    hUn.trans (le_trans (min_le_left _ _) (min_le_left _ _))
  have hT₄ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ₄ :=
    hTn.trans (le_trans (min_le_left _ _) (min_le_right _ _))
  have hU₄ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ₄ :=
    hUn.trans (le_trans (min_le_left _ _) (min_le_right _ _))
  have hTb₂ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρb₂ :=
    hTn.trans (le_trans (min_le_right _ _) (min_le_left _ _))
  have hUb₂ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρb₂ :=
    hUn.trans (le_trans (min_le_right _ _) (min_le_left _ _))
  have hTb₄ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρb₄ :=
    hTn.trans (le_trans (min_le_right _ _) (min_le_right _ _))
  set N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have htel :
      cometricDoublePairTraceCoefficient (I := I) (M := M) g gT -
          cometricDoublePairTraceCoefficient (I := I) (M := M) g gU =
        ccOperatorFieldComp (I := I) (M := M) g 6 4 2
            (pureTrace (I := I) (M := M) g gU 2)
            (pureTrace (I := I) (M := M) g gT 4 -
              pureTrace (I := I) (M := M) g gU 4) +
          ccOperatorFieldComp (I := I) (M := M) g 6 4 2
            (pureTrace (I := I) (M := M) g gT 2 -
              pureTrace (I := I) (M := M) g gU 2)
            (pureTrace (I := I) (M := M) g gT 4) := by
    rw [lcvPair_eq_lip, lcvPair_eq_lip,
      operatorFieldComposition_sub_right, operatorFieldComposition_sub_left]
    module
  have hXraw := happ
    (pureTrace (I := I) (M := M) g gU 2)
    (pureTrace (I := I) (M := M) g gT 4 -
      pureTrace (I := I) (M := M) g gU 4)
  have hYraw := happ
    (pureTrace (I := I) (M := M) g gT 2 -
      pureTrace (I := I) (M := M) g gU 2)
    (pureTrace (I := I) (M := M) g gT 4)
  have hb₂U := hb₂ U gU hUtie hUb₂
  have hb₄T := hb₄ T gT hTtie hTb₄
  have hp₂TU := hp₂ T U gT gU hTtie hUtie hT₂ hU₂
  have hp₄TU := hp₄ T U gT gU hTtie hUtie hT₄ hU₄
  set j2U : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (pureTrace (I := I) (M := M) g gU 2) with hj2U
  set j4T : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (pureTrace (I := I) (M := M) g gT 4) with hj4T
  set j2d : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (pureTrace (I := I) (M := M) g gT 2 -
      pureTrace (I := I) (M := M) g gU 2) with hj2d
  set j4d : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (pureTrace (I := I) (M := M) g gT 4 -
      pureTrace (I := I) (M := M) g gU 4) with hj4d
  have hj2U0 : 0 ≤ j2U := jet_nonneg_lip (I := I) (M := M) g _
  have hj4T0 : 0 ≤ j4T := jet_nonneg_lip (I := I) (M := M) g _
  have hj2d0 : 0 ≤ j2d := jet_nonneg_lip (I := I) (M := M) g _
  have hj4d0 : 0 ≤ j4d := jet_nonneg_lip (I := I) (M := M) g _
  have hsq :
      Real.sqrt (2 * (Ca * B₂ ^ 2 * C₄ ^ 2 +
          Ca * C₂ ^ 2 * B₄ ^ 2)) ^ 2 =
        2 * (Ca * B₂ ^ 2 * C₄ ^ 2 + Ca * C₂ ^ 2 * B₄ ^ 2) := by
    exact Real.sq_sqrt (by positivity)
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gT -
          cometricDoublePairTraceCoefficient (I := I) (M := M) g gU) =
      covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g 6 4 2
            (pureTrace (I := I) (M := M) g gU 2)
            (pureTrace (I := I) (M := M) g gT 4 -
              pureTrace (I := I) (M := M) g gU 4) +
          ccOperatorFieldComp (I := I) (M := M) g 6 4 2
            (pureTrace (I := I) (M := M) g gT 2 -
              pureTrace (I := I) (M := M) g gU 2)
            (pureTrace (I := I) (M := M) g gT 4)) := by
      rw [htel]
    _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 6 4 2
            (pureTrace (I := I) (M := M) g gU 2)
            (pureTrace (I := I) (M := M) g gT 4 -
              pureTrace (I := I) (M := M) g gU 4)) +
        covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 6 4 2
            (pureTrace (I := I) (M := M) g gT 2 -
              pureTrace (I := I) (M := M) g gU 2)
            (pureTrace (I := I) (M := M) g gT 4))) :=
      jet_add_lip (I := I) (M := M) g 2 _ _
    _ ≤ 2 * (Ca * j2U * j4d + Ca * j2d * j4T) := by
      linarith [hXraw, hYraw]
    _ ≤ 2 * (Ca * B₂ ^ 2 * ((C₄ * N) ^ 2) +
        Ca * ((C₂ * N) ^ 2) * B₄ ^ 2) := by
      have h1 : Ca * j2U * j4d ≤ Ca * B₂ ^ 2 * ((C₄ * N) ^ 2) := by
        have hu : j2U ≤ B₂ ^ 2 := by rw [hj2U]; exact hb₂U
        have hd : j4d ≤ (C₄ * N) ^ 2 := by rw [hj4d, hN]; exact hp₄TU
        have hstep := mul_le_mul hu hd hj4d0
          (le_trans hj2U0 hu)
        calc
          Ca * j2U * j4d = Ca * (j2U * j4d) := by ring
          _ ≤ Ca * (B₂ ^ 2 * ((C₄ * N) ^ 2)) :=
            mul_le_mul_of_nonneg_left hstep hCa
          _ = Ca * B₂ ^ 2 * ((C₄ * N) ^ 2) := by ring
      have h2 : Ca * j2d * j4T ≤ Ca * ((C₂ * N) ^ 2) * B₄ ^ 2 := by
        have hd : j2d ≤ (C₂ * N) ^ 2 := by rw [hj2d, hN]; exact hp₂TU
        have hu : j4T ≤ B₄ ^ 2 := by rw [hj4T]; exact hb₄T
        have hstep := mul_le_mul hd hu hj4T0
          (le_trans hj2d0 hd)
        calc
          Ca * j2d * j4T = Ca * (j2d * j4T) := by ring
          _ ≤ Ca * (((C₂ * N) ^ 2) * B₄ ^ 2) :=
            mul_le_mul_of_nonneg_left hstep hCa
          _ = Ca * ((C₂ * N) ^ 2) * B₄ ^ 2 := by ring
      linarith
    _ = (Real.sqrt (2 * (Ca * B₂ ^ 2 * C₄ ^ 2 +
          Ca * C₂ ^ 2 * B₄ ^ 2)) * N) ^ 2 := by
      conv_rhs => rw [mul_pow, hsq]
      ring

omit [SigmaCompactSpace M] in
private theorem riemannianFiberNormSq_term_le_lip
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g (s + 1) ((s + 1 + 1) + i) x
        ((iteratedCovGrad (I := I) g (s + 1) (s + 1 + 1) i
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g s A)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        riemannianFiberNormSq (I := I) (M := M) g 1 (1 + 1 + i) x
          ((iteratedCovGrad (I := I) g 1 (1 + 1) i
            (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0 A)).toSection x) := by
  induction s with
  | zero =>
    rw [pow_zero, one_mul]
  | succ s ih =>
    have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    have hA : riemannianFiberNormSq (I := I) (M := M) g
          (s + 1 + 1) ((s + 1 + 1 + 1) + i) x
          ((iteratedCovGrad (I := I) g (s + 1 + 1) (s + 1 + 1 + 1) i
            (bilinearSlotInsertionCoefficient (I := I) (M := M) g (s + 1) A)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g
          (s + 1 + 1) ((s + 1 + 1 + 1) + i) x
          ((iteratedCovGrad (I := I) g (s + 1 + 1) (s + 1 + 1 + 1) i
            (slotExtend (I := I) (M := M) g (s + 1) (s + 1 + 1)
              (bilinearSlotInsertionCoefficient (I := I) (M := M) g s A))).toSection x) := by
      rw [DifferentialGeometry.Analysis.Sobolev.termSlotEndoCc_succ
        (I := I) (M := M) g s A]
      exact riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g
        (s + 1 + 1) (s + 1 + 1 + 1)
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
        ((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
          (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2))
        (slotExtend (I := I) (M := M) g (s + 1) (s + 1 + 1)
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g s A)) i x
    rw [hA]
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g
      (s + 1) (s + 1 + 1)
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g s A) i x) ?_
    calc (Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g
              (s + 1) ((s + 1 + 1) + i) x
              ((iteratedCovGrad (I := I) g (s + 1) (s + 1 + 1) i
                (bilinearSlotInsertionCoefficient (I := I) (M := M) g s A)).toSection x)
        ≤ (Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) ^ s *
              riemannianFiberNormSq (I := I) (M := M) g 1 (1 + 1 + i) x
                ((iteratedCovGrad (I := I) g 1 (1 + 1) i
                  (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0 A)).toSection x)) :=
          mul_le_mul_of_nonneg_left ih hfr
      _ = (Module.finrank ℝ E : ℝ) ^ (s + 1) *
            riemannianFiberNormSq (I := I) (M := M) g 1 (1 + 1 + i) x
              ((iteratedCovGrad (I := I) g 1 (1 + 1) i
                (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0 A)).toSection x) := by
          rw [pow_succ]
          ring

private theorem term_l2_lip
    (g : SmoothRiemannianMetric I M) (s i : ℕ)
    (A : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    ‖iteratedCovGrad (I := I) g (s + 1) (s + 1 + 1) i
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g s A)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 (1 + 1) i
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0 A)‖ ^ 2 := by
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) ^ s *
    riemannianFiberNormSq (I := I) (M := M) g 1 (1 + 1 + i) x
      ((iteratedCovGrad (I := I) g 1 (1 + 1) i
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0 A)).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g 1 (1 + 1 + i)
      (iteratedCovGrad (I := I) g 1 (1 + 1) i
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0 A))).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (s + 1) ((s + 1 + 1) + i)
    (iteratedCovGrad (I := I) g (s + 1) (s + 1 + 1) i
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g s A))
    F hF (fun x =>
      riemannianFiberNormSq_term_le_lip (I := I) (M := M) g s A i x)
  have hint : (∫ x,
      riemannianFiberNormSq (I := I) (M := M) g 1 (1 + 1 + i) x
        ((iteratedCovGrad (I := I) g 1 (1 + 1) i
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0 A)).toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ‖iteratedCovGrad (I := I) g 1 (1 + 1) i
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0 A)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g 1 (1 + 1 + i)]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

private theorem term_h1_lip
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    covariantJetNormSq (I := I) (M := M) g 1
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g s A) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        covariantJetNormSq (I := I) (M := M) g 1
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0 A) := by
  unfold covariantJetNormSq
  calc
    ∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1 + 1) i
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g s A)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 2, (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 (1 + 1) i
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0 A)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        term_l2_lip (I := I) (M := M) g s i A
    _ = (Module.finrank ℝ E : ℝ) ^ s *
        ∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 1 (1 + 1) i
            (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0 A)‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem term_h2_lip
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    covariantJetNormSq (I := I) (M := M) g 2
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g s A) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        covariantJetNormSq (I := I) (M := M) g 2
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0 A) := by
  unfold covariantJetNormSq
  calc
    ∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1 + 1) i
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g s A)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 3, (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 (1 + 1) i
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0 A)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        term_l2_lip (I := I) (M := M) g s i A
    _ = (Module.finrank ℝ E : ℝ) ^ s *
        ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 1 (1 + 1) i
            (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0 A)‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem termU_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gT)) ≤
        (((Module.finrank ℝ E : ℝ)) * B R * A) ^ 2 := by
  obtain ⟨Bs, hBs, hwSelf⟩ :=
    wXi_self_tame (I := I) (M := M) hDim g
  refine ⟨Bs, hBs, ?_⟩
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have hbase : bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
      (connectionDifferenceEndomorphism (I := I) (M := M) g gT) =
      connectionDifferenceSection (I := I) gT g :=
    (connectionDifferenceSection_eq_bilinearSlotInsertionCoefficient_zero
      (I := I) (M := M) g gT).symm
  have hw := hwSelf gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have h0 : covariantJetNormSq (I := I) (M := M) g 2
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
        (connectionDifferenceEndomorphism (I := I) (M := M) g gT)) ≤
      (Bs R * A) ^ 2 := by
    rw [hbase, connSec_self_h2 (I := I) (M := M) g gT]
    exact hw
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gT)) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
            (connectionDifferenceEndomorphism (I := I) (M := M) g gT)) :=
      term_h2_lip (I := I) (M := M) g 2
        (connectionDifferenceEndomorphism (I := I) (M := M) g gT)
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (Bs R * A) ^ 2 :=
      mul_le_mul_of_nonneg_left h0
        (pow_nonneg (Nat.cast_nonneg _) 2)
    _ = (((Module.finrank ℝ E : ℝ)) * Bs R * A) ^ 2 := by ring

private theorem termD_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 1
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
            bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) ≤
        (((Module.finrank ℝ E : ℝ)) * B0 R * D2 +
          ((Module.finrank ℝ E : ℝ)) * B1 R * A * D2) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ :=
    connSec_pair_h1 (I := I) (M := M) hDim g hδ₀0 hδ₀
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 hR hA hD2 hU2 hT3 hTU2
  have hp := hpair gT gU T U hT hU hTtie hUtie
    hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 hR hA hD2 hU2 hT3 hTU2
  have hsub : bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
        (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
      bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
        (connectionDifferenceEndomorphism (I := I) (M := M) g gU) =
      bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
        (connectionDifferenceEndomorphism (I := I) (M := M) g gT -
          connectionDifferenceEndomorphism (I := I) (M := M) g gU) :=
    (DifferentialGeometry.Analysis.Sobolev.termSlotEndoCc_sub
      (I := I) (M := M) g 2 _ _).symm
  have hsub0 : bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
        (connectionDifferenceEndomorphism (I := I) (M := M) g gT -
          connectionDifferenceEndomorphism (I := I) (M := M) g gU) =
      connectionDifferenceSection (I := I) gT g -
        connectionDifferenceSection (I := I) gU g := by
    rw [DifferentialGeometry.Analysis.Sobolev.termSlotEndoCc_sub
      (I := I) (M := M) g 0 _ _,
      ← connectionDifferenceSection_eq_bilinearSlotInsertionCoefficient_zero
        (I := I) (M := M) g gT,
      ← connectionDifferenceSection_eq_bilinearSlotInsertionCoefficient_zero
        (I := I) (M := M) g gU]
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
          bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) =
      covariantJetNormSq (I := I) (M := M) g 1
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gT -
            connectionDifferenceEndomorphism (I := I) (M := M) g gU)) := by
      rw [hsub]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 1
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
            (connectionDifferenceEndomorphism (I := I) (M := M) g gT -
              connectionDifferenceEndomorphism (I := I) (M := M) g gU)) :=
      term_h1_lip (I := I) (M := M) g 2 _
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 1
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g) := by
      rw [hsub0]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
        (B0 R * D2 + B1 R * A * D2) ^ 2 :=
      mul_le_mul_of_nonneg_left hp
        (pow_nonneg (Nat.cast_nonneg _) 2)
    _ = (((Module.finrank ℝ E : ℝ)) * B0 R * D2 +
        ((Module.finrank ℝ E : ℝ)) * B1 R * A * D2) ^ 2 := by
      ring

private theorem lcvPair_h2_bdd
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (gT : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        covariantJetNormSq (I := I) (M := M) g 2
            (cometricDoublePairTraceCoefficient (I := I) (M := M) g gT) ≤ B := by
  obtain ⟨ρb₂, B₂, hρb₂, hB₂, hb₂⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρb₄, B₄, hρb₄, hB₄, hb₄⟩ :=
    RicciDeTurckLowOrder.trace_four_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul_lip (I := I) (M := M) hDim g 6 4 2
  refine ⟨min ρb₂ ρb₄, Ca * B₂ ^ 2 * B₄ ^ 2,
    lt_min hρb₂ hρb₄, by positivity, ?_⟩
  intro T gT hTtie hTn
  have hT₂ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρb₂ :=
    hTn.trans (min_le_left _ _)
  have hT₄ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρb₄ :=
    hTn.trans (min_le_right _ _)
  have hb₂T := hb₂ T gT hTtie hT₂
  have hb₄T := hb₄ T gT hTtie hT₄
  have hraw := happ
    (pureTrace (I := I) (M := M) g gT 2)
    (pureTrace (I := I) (M := M) g gT 4)
  have hj2 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
      (pureTrace (I := I) (M := M) g gT 2) :=
    jet_nonneg_lip (I := I) (M := M) g _
  have hj4 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
      (pureTrace (I := I) (M := M) g gT 4) :=
    jet_nonneg_lip (I := I) (M := M) g _
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gT) =
      covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g 6 4 2
          (pureTrace (I := I) (M := M) g gT 2)
          (pureTrace (I := I) (M := M) g gT 4)) := by
      rw [lcvPair_eq_lip]
    _ ≤ Ca * covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gT 2) *
        covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gT 4) := hraw
    _ ≤ Ca * B₂ ^ 2 * B₄ ^ 2 := by
      have hstep := mul_le_mul hb₂T hb₄T hj4
        (le_trans hj2 hb₂T)
      calc
        Ca * covariantJetNormSq (I := I) (M := M) g 2
              (pureTrace (I := I) (M := M) g gT 2) *
            covariantJetNormSq (I := I) (M := M) g 2
              (pureTrace (I := I) (M := M) g gT 4) =
          Ca * (covariantJetNormSq (I := I) (M := M) g 2
              (pureTrace (I := I) (M := M) g gT 2) *
            covariantJetNormSq (I := I) (M := M) g 2
              (pureTrace (I := I) (M := M) g gT 4)) := by ring
        _ ≤ Ca * (B₂ ^ 2 * B₄ ^ 2) :=
          mul_le_mul_of_nonneg_left hstep hCa
        _ = Ca * B₂ ^ 2 * B₄ ^ 2 := by ring

theorem lieOmega_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 D3 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lipOmega (I := I) (M := M) g gT -
            lipOmega (I := I) (M := M) g gU) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨C, hC, hpair⟩ :=
    omega_pair (I := I) (M := M) hDim g
  obtain ⟨Cr, hCr, hrevB⟩ :=
    RicciDeTurckLowOrder.reverse_slot_sobolev_two_bound (I := I) (M := M) g
  obtain ⟨Bs, hBs, hwSelf⟩ :=
    wXi_self_tame (I := I) (M := M) hDim g
  obtain ⟨W0, W1, hW0, hW1, hwDiff⟩ :=
    exists_metricLoweredConnectionDifference_covariantJetNormSq_two_sub_tame_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let Hc : ℝ := Real.sqrt C
  let fr : ℝ := Module.finrank ℝ E
  let B0 : ℝ → ℝ := fun R =>
    Hc * (Cr * (1 + R)) * W0 R
  let B1 : ℝ → ℝ := fun R =>
    Hc * (Cr * (1 + R) * W1 R + fr * Bs R)
  have hHc : 0 ≤ Hc := Real.sqrt_nonneg _
  have hHcSq : Hc ^ 2 = C := by
    simpa only [Hc] using Real.sq_sqrt hC
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨B0, B1, ?_, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg
      (mul_nonneg hHc (mul_nonneg hCr (add_nonneg (by norm_num) hR)))
      (hW0 R hR)
  · intro R hR
    exact mul_nonneg hHc
      (add_nonneg
        (mul_nonneg
          (mul_nonneg hCr (add_nonneg (by norm_num) hR)) (hW1 R hR))
        (mul_nonneg hfr (hBs R hR)))
  intro gT gU T U hT hU hTtie hUtie
    δ hδ_le hδ0 hδT hδU hδZ
    R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hTU2 hTU3
  let AU : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (slotInsertEndoCc (I := I) (M := M) g 2
      (metricComparisonEndomorphismField (I := I) (M := M) gU g))
  let AD : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M) gT g) -
      slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M) gU g))
  let WT : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (metricLoweredConnectionDifference (I := I) (M := M) g gT g)
  let WD : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (metricLoweredConnectionDifference (I := I) (M := M) g gT g -
      metricLoweredConnectionDifference (I := I) (M := M) g gU g)
  let X : ℝ := W0 R * D3 + W1 R * D2 + W1 R * A * D2
  let P : ℝ := Cr * (1 + R)
  let Q : ℝ := fr * Bs R
  let L : ℝ := Hc * (P * X + Q * A * D2)
  let Z : ℝ := B0 R * D3 + B1 R * D2 + B1 R * A * D2
  have hAU0 : 0 ≤ AU := jet_nonneg_lip (I := I) (M := M) g _
  have hAD0 : 0 ≤ AD := jet_nonneg_lip (I := I) (M := M) g _
  have hWT0 : 0 ≤ WT := jet_nonneg_lip (I := I) (M := M) g _
  have hWD0 : 0 ≤ WD := jet_nonneg_lip (I := I) (M := M) g _
  have hW0R : 0 ≤ W0 R := hW0 R hR
  have hW1R : 0 ≤ W1 R := hW1 R hR
  have hBsR : 0 ≤ Bs R := hBs R hR
  have hP : 0 ≤ P :=
    mul_nonneg hCr (add_nonneg (by norm_num) hR)
  have hQ : 0 ≤ Q := mul_nonneg hfr hBsR
  have hX : 0 ≤ X := by
    exact add_nonneg
      (add_nonneg (mul_nonneg hW0R hD3) (mul_nonneg hW1R hD2))
      (mul_nonneg (mul_nonneg hW1R hA) hD2)
  have hAU :
      AU ≤ P ^ 2 := by
    simpa only [AU, P] using
      hrevB gU U hU hUtie R hR hU2
  have hAD :
      AD ≤ (fr * D2) ^ 2 := by
    have hraw :=
      RicciDeTurckLowOrder.revSlot_pair_h2 (I := I) (M := M)
        g gT gU T U hT hU hTtie hUtie
    calc
      AD ≤ fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 (T - U) := by
        simpa only [AD, fr] using hraw
      _ ≤ fr ^ 2 * D2 ^ 2 :=
        mul_le_mul_of_nonneg_left hTU2 (sq_nonneg fr)
      _ = (fr * D2) ^ 2 := by ring
  have hWT :
      WT ≤ (Bs R * A) ^ 2 := by
    simpa only [WT] using
      hwSelf gT T hT hTtie hδ_le hδ0 hδT hδZ
        R A hR hA hT2 hT3
  have hWD :
      WD ≤ X ^ 2 := by
    simpa only [WD, X] using
      hwDiff gT gU g T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have hPairRaw :
      covariantJetNormSq (I := I) (M := M) g 2
          (lipOmega (I := I) (M := M) g gT -
            lipOmega (I := I) (M := M) g gU) ≤
        C * (AU * WD + AD * WT) := by
    simpa only [AU, AD, WT, WD, metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc] using hpair gT gU
  have hFirst : AU * WD ≤ (P * X) ^ 2 := by
    calc
      AU * WD ≤ P ^ 2 * X ^ 2 :=
        mul_le_mul hAU hWD hWD0 (sq_nonneg P)
      _ = (P * X) ^ 2 := by ring
  have hSecond : AD * WT ≤ (Q * A * D2) ^ 2 := by
    calc
      AD * WT ≤ (fr * D2) ^ 2 * (Bs R * A) ^ 2 :=
        mul_le_mul hAD hWT hWT0 (sq_nonneg (fr * D2))
      _ = (Q * A * D2) ^ 2 := by
        simp only [Q]
        ring
  have hPX : 0 ≤ P * X := mul_nonneg hP hX
  have hQAD : 0 ≤ Q * A * D2 :=
    mul_nonneg (mul_nonneg hQ hA) hD2
  have hL0 : 0 ≤ L :=
    mul_nonneg hHc (add_nonneg hPX hQAD)
  have hToL :
      C * (AU * WD + AD * WT) ≤ L ^ 2 := by
    calc
      C * (AU * WD + AD * WT) ≤
          C * ((P * X) ^ 2 + (Q * A * D2) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond) hC
      _ ≤ C * (P * X + Q * A * D2) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact sq_add_sq_le_sum_sq hPX hQAD
      _ = L ^ 2 := by
        simp only [L]
        rw [mul_pow, hHcSq]
  have hZeq : Z = L + Hc * Q * D2 := by
    simp only [Z, L, B0, B1, P, Q, X]
    ring
  have hLZ : L ≤ Z := by
    rw [hZeq]
    exact le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg hHc hQ) hD2)
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (lipOmega (I := I) (M := M) g gT -
          lipOmega (I := I) (M := M) g gU) ≤
      C * (AU * WD + AD * WT) := hPairRaw
    _ ≤ L ^ 2 := hToL
    _ ≤ Z ^ 2 := pow_le_pow_left₀ hL0 hLZ 2
    _ = (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := rfl

theorem lie_omega_sobolev_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lipOmega (I := I) (M := M) g gT) ≤
        (B R * A) ^ 2 := by
  obtain ⟨C, hC, happ⟩ :=
    app_h2_mul_lip (I := I) (M := M) hDim g 0 3 3
  obtain ⟨Cr, hCr, hrevB⟩ :=
    RicciDeTurckLowOrder.reverse_slot_sobolev_two_bound (I := I) (M := M) g
  obtain ⟨Bs, hBs, hwSelf⟩ :=
    wXi_self_tame (I := I) (M := M) hDim g
  let Hc : ℝ := Real.sqrt C
  let B : ℝ → ℝ := fun R =>
    Hc * Cr * (1 + R) * Bs R
  have hHc : 0 ≤ Hc := Real.sqrt_nonneg _
  have hHcSq : Hc ^ 2 = C := by
    simpa only [Hc] using Real.sq_sqrt hC
  refine ⟨B, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hHc hCr) (by linarith))
      (hBs R hR)
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  let RF : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2
      (metricComparisonEndomorphismField (I := I) (M := M) gT g)
  let CD : SmoothCcTensor g 0 3 :=
    domDomCongrSection (I := I) g (finRotate 3)
      (metricLoweredConnectionDifferenceCoefficient (I := I) g gT)
  have hRF0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 RF :=
    jet_nonneg_lip (I := I) (M := M) g RF
  have hCD0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 CD :=
    jet_nonneg_lip (I := I) (M := M) g CD
  have hRF :
      covariantJetNormSq (I := I) (M := M) g 2 RF ≤
        (Cr * (1 + R)) ^ 2 := by
    simpa only [RF] using hrevB gT T hT hTtie R hR hT2
  have hCD :
      covariantJetNormSq (I := I) (M := M) g 2 CD ≤
        (Bs R * A) ^ 2 := by
    rw [dom_h2_lip]
    simpa only [metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc] using
      hwSelf gT T hT hTtie hδ_le hδ0 hδT hδZ
        R A hR hA hT2 hT3
  have hraw := happ RF CD
  change covariantJetNormSq (I := I) (M := M) g 2
      (lipOmega (I := I) (M := M) g gT) ≤
    C * covariantJetNormSq (I := I) (M := M) g 2 RF *
      covariantJetNormSq (I := I) (M := M) g 2 CD at hraw
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (lipOmega (I := I) (M := M) g gT) ≤
      C * covariantJetNormSq (I := I) (M := M) g 2 RF *
        covariantJetNormSq (I := I) (M := M) g 2 CD := hraw
    _ ≤ C * (Cr * (1 + R)) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2 CD :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hRF hC) hCD0
    _ ≤ C * (Cr * (1 + R)) ^ 2 * (Bs R * A) ^ 2 :=
      mul_le_mul_of_nonneg_left hCD
        (mul_nonneg hC (sq_nonneg _))
    _ = (B R * A) ^ 2 := by
      simp only [B]
      rw [← hHcSq]
      ring

private theorem hat_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT) ≤
        (B R * A) ^ 2 := by
  obtain ⟨B, hB, hbdd⟩ :=
    lie_omega_sobolev_two_bound (I := I) (M := M) hDim g
  refine ⟨B, hB, ?_⟩
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  rw [hat_eq_lip (I := I) (M := M) g gT]
  exact hbdd gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
private theorem curvF_zero_lip
    (g : SmoothRiemannianMetric I M) :
    riemannCurvatureCoefficientField (I := I) (M := M) g (0 : SmoothCcTensor g 0 2) = 0 := by
  simp only [riemannCurvatureCoefficientField, riemannCurvatureCoefficientField,
    operatorFieldComposition_zero_right, add_zero]

private theorem curvF_bdd_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2),
        covariantJetNormSq (I := I) (M := M) g 1
            (riemannCurvatureCoefficientField (I := I) (M := M) g T) ≤
          C * covariantJetNormSq (I := I) (M := M) g 2 T := by
  obtain ⟨C, hC, hpair⟩ :=
    curvF_pair_h1 (I := I) (M := M) hDim g
  refine ⟨C, hC, ?_⟩
  intro T
  have h := hpair T 0
  rw [curvF_zero_lip (I := I) (M := M) g, sub_zero, sub_zero] at h
  exact h

private theorem quadF_bdd_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 1
          (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gT) ≤
        (B R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 0 3 4
  obtain ⟨Ba, hBa, harm⟩ :=
    termU_bdd_h2 (I := I) (M := M) hDim g
  obtain ⟨Bh, hBh, hhat⟩ :=
    hat_bdd_h2 (I := I) (M := M) hDim g
  let fr : ℝ := (Module.finrank ℝ E : ℝ)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  let B : ℝ → ℝ := fun R =>
    Real.sqrt (384 * C₀) * (fr * Ba R) * Bh R
  refine ⟨B, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg hfr (hBa R hR)))
      (hBh R hR)
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have harmB := harm gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have hhatB := hhat gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  set c : SmoothCcTensor g 3 4 :=
    bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
      (connectionDifferenceEndomorphism (I := I) (M := M) g gT) with hc
  set w : SmoothCcTensor g 0 3 :=
    connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT with hw
  have hhat1 : covariantJetNormSq (I := I) (M := M) g 1 w ≤ (Bh R * A) ^ 2 :=
    le_trans (jet_mono_lip (I := I) (M := M) g (by norm_num) w) hhatB
  have hQBapp : connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gT =
      ccOperatorFieldComp (I := I) (M := M) g 0 3 4 c w := rfl
  have hQAapp : connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT =
      ccOperatorFieldComp (I := I) (M := M) g 0 3 4 c
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1) w) := rfl
  set K : ℝ := C₀ * ((fr * Ba R * A) ^ 2) * ((Bh R * A) ^ 2) with hK
  have hK0 : 0 ≤ K :=
    mul_nonneg (mul_nonneg hC₀ (sq_nonneg _)) (sq_nonneg _)
  set x : ℝ := covariantJetNormSq (I := I) (M := M) g 1
    (connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gT) with hxdef
  set y : ℝ := covariantJetNormSq (I := I) (M := M) g 1
    (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT) with hydef
  have hx : x ≤ K := by
    rw [hxdef, hQBapp, hK]
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g 0 3 4 c w) ≤
        C₀ * covariantJetNormSq (I := I) (M := M) g 2 c *
          covariantJetNormSq (I := I) (M := M) g 1 w := happ c w
      _ ≤ C₀ * ((fr * Ba R * A) ^ 2) * ((Bh R * A) ^ 2) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left harmB hC₀)
          hhat1
          (jet_nonneg_lip (I := I) (M := M) g w)
          (mul_nonneg hC₀ (sq_nonneg _))
  have hy : y ≤ K := by
    rw [hydef, hQAapp, hK]
    have hd := dom_h1_lip (I := I) (M := M) g
      (Equiv.swap (0 : Fin 3) 1) w
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g 0 3 4 c
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 3) 1) w)) ≤
        C₀ * covariantJetNormSq (I := I) (M := M) g 2 c *
          covariantJetNormSq (I := I) (M := M) g 1
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 3) 1) w) :=
        happ c _
      _ = C₀ * covariantJetNormSq (I := I) (M := M) g 2 c *
          covariantJetNormSq (I := I) (M := M) g 1 w := by rw [hd]
      _ ≤ C₀ * ((fr * Ba R * A) ^ 2) * ((Bh R * A) ^ 2) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left harmB hC₀)
          hhat1
          (jet_nonneg_lip (I := I) (M := M) g w)
          (mul_nonneg hC₀ (sq_nonneg _))
  have hsplit :
      connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gT =
        domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1)
            (connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gT) +
          (connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gT +
            (domDomCongrSection (I := I) g lrPermA
                (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT) +
              (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2)
                  (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT) +
                (domDomCongrSection (I := I) g lrPermB
                    (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT) +
                  domDomCongrSection (I := I) g lrPermC
                    (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT))))) := by
    simp only [connectionDifferenceQuadraticCurvatureTerm, connectionDifferenceQuadraticCurvatureTerm, connectionDifferenceQuadraticPairedTensor, connectionDifferenceQuadraticComposedTensor]
    abel
  set QB : SmoothCcTensor g 0 4 := connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gT with hQB
  set QA : SmoothCcTensor g 0 4 := connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT with hQA
  have hd1 : covariantJetNormSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) QB) =
      covariantJetNormSq (I := I) (M := M) g 1 QB :=
    dom_h1_lip (I := I) (M := M) g _ _
  have hd3 : covariantJetNormSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermA QA) =
      covariantJetNormSq (I := I) (M := M) g 1 QA :=
    dom_h1_lip (I := I) (M := M) g _ _
  have hd4 : covariantJetNormSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QA) =
      covariantJetNormSq (I := I) (M := M) g 1 QA :=
    dom_h1_lip (I := I) (M := M) g _ _
  have hd5 : covariantJetNormSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermB QA) =
      covariantJetNormSq (I := I) (M := M) g 1 QA :=
    dom_h1_lip (I := I) (M := M) g _ _
  have hd6 : covariantJetNormSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermC QA) =
      covariantJetNormSq (I := I) (M := M) g 1 QA :=
    dom_h1_lip (I := I) (M := M) g _ _
  have h56 : covariantJetNormSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermB QA +
        domDomCongrSection (I := I) g lrPermC QA) ≤
      2 * (covariantJetNormSq (I := I) (M := M) g 1 QA +
        covariantJetNormSq (I := I) (M := M) g 1 QA) := by
    linarith [jet_add_lip (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g lrPermB QA)
        (domDomCongrSection (I := I) g lrPermC QA),
      hd5, hd6]
  have h456 : covariantJetNormSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QA +
        (domDomCongrSection (I := I) g lrPermB QA +
          domDomCongrSection (I := I) g lrPermC QA)) ≤
      2 * covariantJetNormSq (I := I) (M := M) g 1 QA +
        2 * (2 * (covariantJetNormSq (I := I) (M := M) g 1 QA +
          covariantJetNormSq (I := I) (M := M) g 1 QA)) := by
    linarith [jet_add_lip (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QA)
        (domDomCongrSection (I := I) g lrPermB QA +
          domDomCongrSection (I := I) g lrPermC QA),
      hd4, h56]
  have h3456 : covariantJetNormSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermA QA +
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QA +
          (domDomCongrSection (I := I) g lrPermB QA +
            domDomCongrSection (I := I) g lrPermC QA))) ≤
      2 * covariantJetNormSq (I := I) (M := M) g 1 QA +
        2 * (2 * covariantJetNormSq (I := I) (M := M) g 1 QA +
          2 * (2 * (covariantJetNormSq (I := I) (M := M) g 1 QA +
            covariantJetNormSq (I := I) (M := M) g 1 QA))) := by
    linarith [jet_add_lip (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g lrPermA QA)
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QA +
          (domDomCongrSection (I := I) g lrPermB QA +
            domDomCongrSection (I := I) g lrPermC QA)),
      hd3, h456]
  have h23456 : covariantJetNormSq (I := I) (M := M) g 1
      (QB +
        (domDomCongrSection (I := I) g lrPermA QA +
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QA +
            (domDomCongrSection (I := I) g lrPermB QA +
              domDomCongrSection (I := I) g lrPermC QA)))) ≤
      2 * covariantJetNormSq (I := I) (M := M) g 1 QB +
        2 * (2 * covariantJetNormSq (I := I) (M := M) g 1 QA +
          2 * (2 * covariantJetNormSq (I := I) (M := M) g 1 QA +
            2 * (2 * (covariantJetNormSq (I := I) (M := M) g 1 QA +
              covariantJetNormSq (I := I) (M := M) g 1 QA)))) := by
    linarith [jet_add_lip (I := I) (M := M) g 1 QB
        (domDomCongrSection (I := I) g lrPermA QA +
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QA +
            (domDomCongrSection (I := I) g lrPermB QA +
              domDomCongrSection (I := I) g lrPermC QA))),
      h3456]
  have hlift : covariantJetNormSq (I := I) (M := M) g 1
      (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gT) ≤
      2 * x + 2 * (2 * x + 2 * (2 * y + 2 * (2 * y +
        2 * (2 * (y + y))))) := by
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gT) =
        covariantJetNormSq (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) QB +
            (QB +
              (domDomCongrSection (I := I) g lrPermA QA +
                (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QA +
                  (domDomCongrSection (I := I) g lrPermB QA +
                    domDomCongrSection (I := I) g lrPermC QA))))) := by
        rw [← hsplit]
      _ ≤ 2 * covariantJetNormSq (I := I) (M := M) g 1 QB +
          2 * (2 * covariantJetNormSq (I := I) (M := M) g 1 QB +
            2 * (2 * covariantJetNormSq (I := I) (M := M) g 1 QA +
              2 * (2 * covariantJetNormSq (I := I) (M := M) g 1 QA +
                2 * (2 * (covariantJetNormSq (I := I) (M := M) g 1 QA +
                  covariantJetNormSq (I := I) (M := M) g 1 QA))))) := by
        linarith [jet_add_lip (I := I) (M := M) g 1
            (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) QB)
            (QB +
              (domDomCongrSection (I := I) g lrPermA QA +
                (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QA +
                  (domDomCongrSection (I := I) g lrPermB QA +
                    domDomCongrSection (I := I) g lrPermC QA)))),
          hd1, h23456]
      _ = 2 * x + 2 * (2 * x + 2 * (2 * y + 2 * (2 * y +
          2 * (2 * (y + y))))) := by
        rw [hxdef, hydef]
  have hKfin : covariantJetNormSq (I := I) (M := M) g 1
      (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gT) ≤ 384 * K := by
    exact hlift.trans (quad_nested_le hK0 hx hy)
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gT) ≤ 384 * K := hKfin
    _ = 384 * C₀ * (fr * Ba R) ^ 2 * (Bh R) ^ 2 * (A ^ 2 * A ^ 2) := by
      rw [hK]; ring
    _ ≤ 384 * C₀ * (fr * Ba R) ^ 2 * (Bh R) ^ 2 * (A + A ^ 2) ^ 2 := by
      exact mul_le_mul_of_nonneg_left (sq_mul_sq_le_add_sq_sq hA)
        (by positivity)
    _ = (B R * (A + A ^ 2)) ^ 2 := by
      have hsq : Real.sqrt (384 * C₀) ^ 2 = 384 * C₀ :=
        Real.sq_sqrt (by positivity)
      simp only [B]
      rw [show (Real.sqrt (384 * C₀) * (fr * Ba R) * Bh R *
            (A + A ^ 2)) ^ 2 =
          Real.sqrt (384 * C₀) ^ 2 *
            ((fr * Ba R) ^ 2 * (Bh R ^ 2 * (A + A ^ 2) ^ 2)) from by
            ring,
        hsq]
      ring

private theorem r4_bdd_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s) ≤
        (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨Cc, hCc, hcurv⟩ :=
    curvF_bdd_h1 (I := I) (M := M) hDim g
  obtain ⟨Bq, hBq, hquad⟩ :=
    quadF_bdd_h1 (I := I) (M := M) hDim g
  let D : ℝ → ℝ := fun R =>
    Real.sqrt (2 * Cc + 2 * (Bq R) ^ 2)
  refine ⟨D, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgm
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) :=
    unit_interval_sq_le_one_lip hs.1 hs.2
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgm, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem
        (I := I) g T 0 hδT hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.2),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hP3 : covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hQF := hquad gm P hPsymm hPtie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3
  have hCF : covariantJetNormSq (I := I) (M := M) g 1
      (riemannCurvatureCoefficientField (I := I) (M := M) g T) ≤ Cc * A ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (riemannCurvatureCoefficientField (I := I) (M := M) g T) ≤
        Cc * covariantJetNormSq (I := I) (M := M) g 2 T := hcurv T
      _ ≤ Cc * covariantJetNormSq (I := I) (M := M) g 3 T :=
        mul_le_mul_of_nonneg_left
          (jet_mono_lip (I := I) (M := M) g (by norm_num) T) hCc
      _ ≤ Cc * A ^ 2 := mul_le_mul_of_nonneg_left hT3 hCc
  have hdecomp :
      deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s =
        (-(s / 2) : ℝ) • riemannCurvatureCoefficientField (I := I) (M := M) g T +
          (-1 : ℝ) • connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm := by
    rw [hgm, deTurckLieCovariantDerivativeRemainderTensor_eq (I := I) (M := M) g T hδT hδZ s]
    module
  have hs22 : (s / 2) ^ 2 ≤ 1 :=
    half_sq_le_one_lip hs.1 hs.2
  set u : ℝ := covariantJetNormSq (I := I) (M := M) g 1
    (riemannCurvatureCoefficientField (I := I) (M := M) g T) with hu
  set v : ℝ := covariantJetNormSq (I := I) (M := M) g 1
    (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm) with hv
  have hu0 : 0 ≤ u := jet_nonneg_lip (I := I) (M := M) g _
  have hv0 : 0 ≤ v := jet_nonneg_lip (I := I) (M := M) g _
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s) =
      covariantJetNormSq (I := I) (M := M) g 1
        ((-(s / 2) : ℝ) • riemannCurvatureCoefficientField (I := I) (M := M) g T +
          (-1 : ℝ) • connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm) := by
      rw [hdecomp]
    _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 1
          ((-(s / 2) : ℝ) • riemannCurvatureCoefficientField (I := I) (M := M) g T) +
        covariantJetNormSq (I := I) (M := M) g 1
          ((-1 : ℝ) • connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm)) :=
      jet_add_lip (I := I) (M := M) g 1 _ _
    _ = 2 * ((-(s / 2)) ^ 2 * u + (-1 : ℝ) ^ 2 * v) := by
      rw [jet_smul_lip, jet_smul_lip, hu, hv]
    _ ≤ 2 * (Cc * A ^ 2 + (Bq R * (A + A ^ 2)) ^ 2) := by
      have h1 : (-(s / 2)) ^ 2 * u ≤ Cc * A ^ 2 := by
        have hle : (-(s / 2)) ^ 2 * u ≤ 1 * u := by
          have hss : (-(s / 2)) ^ 2 = (s / 2) ^ 2 := by ring
          rw [hss]
          exact mul_le_mul_of_nonneg_right hs22 hu0
        rw [one_mul] at hle
        exact hle.trans (by rw [hu]; exact hCF)
      have h2 : (-1 : ℝ) ^ 2 * v ≤ (Bq R * (A + A ^ 2)) ^ 2 := by
        have hvv : ((-1 : ℝ) ^ 2 * v) = v := by ring
        rw [hvv, hv]
        exact hQF
      exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num)
    _ ≤ (D R * (A + A ^ 2)) ^ 2 := by
      have hCcA : Cc * A ^ 2 ≤ Cc * (A + A ^ 2) ^ 2 := by
        exact mul_le_mul_of_nonneg_left (sq_le_add_sq_sq hA) hCc
      have hsq : D R ^ 2 = 2 * Cc + 2 * (Bq R) ^ 2 := by
        simp only [D]
        exact Real.sq_sqrt (by positivity)
      have hexp : (D R * (A + A ^ 2)) ^ 2 =
          (2 * Cc + 2 * (Bq R) ^ 2) * (A + A ^ 2) ^ 2 := by
        rw [mul_pow, hsq]
      rw [hexp]
      have hBq2 : ((Bq R) * (A + A ^ 2)) ^ 2 =
          (Bq R) ^ 2 * (A + A ^ 2) ^ 2 := by ring
      calc
        2 * (Cc * A ^ 2 + (Bq R * (A + A ^ 2)) ^ 2) ≤
            2 * (Cc * (A + A ^ 2) ^ 2 +
              (Bq R * (A + A ^ 2)) ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add hCcA le_rfl) (by norm_num)
        _ = (2 * Cc + 2 * (Bq R) ^ 2) * (A + A ^ 2) ^ 2 := by
          rw [hBq2]
          ring

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem edgePair_eq_lip
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
          ![(-1 : ℝ), -1, 1] s := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem rsperm_sub_lip
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : SmoothCcTensor g r s) :
    rsDomDomCongrSection (I := I) (M := M) g r s σ (A - B) =
      rsDomDomCongrSection (I := I) (M := M) g r s σ A -
        rsDomDomCongrSection (I := I) (M := M) g r s σ B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  change rsDomDomCongr σ ((A - B).toSection x) =
    rsDomDomCongr σ (A.toSection x) - rsDomDomCongr σ (B.toSection x)
  rw [show (A - B).toSection x = A.toSection x - B.toSection x from rfl]
  simp only [rsDomDomCongr]
  rfl

private theorem covX_bdd_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 1
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨D, hD, hr4⟩ :=
    r4_bdd_h1 (I := I) (M := M) hDim g
  refine ⟨D, hD, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 s hs
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) :=
    Nat.cast_nonneg _
  have hIter : slotExtendIter (I := I) (M := M) g 0 4 2
      (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s) =
      slotExtend (I := I) (M := M) g 1 5
        (slotExtend (I := I) (M := M) g 0 4
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) := rfl
  have hbase := hr4 T hT hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hs
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) =
      covariantJetNormSq (I := I) (M := M) g 1
        (slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) := by
      rw [hIter, covariantJetNormSq_rsDomDomCongrSection]
    _ ≤ (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 0 4
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) :=
      covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 5 _
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          covariantJetNormSq (I := I) (M := M) g 1
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) :=
      mul_le_mul_of_nonneg_left
        (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 4 _) hfr
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) * (D R * (A + A ^ 2)) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbase hfr) hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 2 * (D R * (A + A ^ 2)) ^ 2 := by
      ring

private theorem covX_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ C R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 1
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
            rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) ≤
        C R * ((1 + A + A ^ 2) ^ 4 * D2 ^ 2) := by
  obtain ⟨Cr, hCr, hr4p⟩ :=
    r4_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨Ba, hBa, harmU⟩ :=
    termU_bdd_h2 (I := I) (M := M) hDim g
  obtain ⟨B0ω, B1ω, hB0ω, hB1ω, hω⟩ :=
    lieOmega_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨B0c, B1c, hB0c, hB1c, harmD⟩ :=
    termD_pair_h1 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bh, hBh, hhatb⟩ :=
    hat_bdd_h2 (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  let C : ℝ → ℝ := fun R =>
    fr ^ 2 * Cr *
      (1 + (fr * Ba R) ^ 2 * (2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2) +
        (2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2) * (Bh R) ^ 2)
  refine ⟨C, ?_, ?_⟩
  · intro R hR
    have h1 : 0 ≤ (fr * Ba R) ^ 2 * (2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    have h2 : 0 ≤ (2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2) *
        (Bh R) ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
    have : (0 : ℝ) ≤ 1 + (fr * Ba R) ^ 2 *
        (2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2) +
        (2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2) * (Bh R) ^ 2 := by
      exact add_nonneg (add_nonneg zero_le_one h1) h2
    exact mul_nonneg (mul_nonneg (sq_nonneg _) hCr) this
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 hR hA hD2 hT2 hU2 hT3 hU3 hTU2 s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) :=
    unit_interval_sq_le_one_lip hs.1 hs.2
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [hcQ, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem
        (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem
        (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.2),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.2),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : covariantJetNormSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    rw [hcQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP3 : covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hQ3 : covariantJetNormSq (I := I) (M := M) g 3 Q ≤ A ^ 2 := by
    rw [hcQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 3) g U) hs2).trans hU3
  have hPQ2 : covariantJetNormSq (I := I) (M := M) g 2 (P - Q) ≤ D2 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g (T - U)) hs2).trans hTU2
  have hXsub :
      rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
        rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)) =
      rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
        (slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
              deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) := by
    rw [← rsperm_sub_lip, slotExtend_sub, slotExtend_sub]
    rfl
  have hfr2 : (0 : ℝ) ≤ fr ^ 2 := sq_nonneg _
  have hXle : covariantJetNormSq (I := I) (M := M) g 1
      (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
        rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) ≤
      fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 1
        (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
          deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s) := by
    rw [hXsub, covariantJetNormSq_rsDomDomCongrSection]
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 1 5
            (slotExtend (I := I) (M := M) g 0 4
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
                deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) ≤
        fr * covariantJetNormSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 0 4
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
              deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 5 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
            deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 4 _) hfr
      _ = fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
            deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s) := by
        ring
  have hr4 := hr4p T U hδT hδU hδZ hs
  rw [← hgmT, ← hgmU] at hr4
  have hJarmQ : covariantJetNormSq (I := I) (M := M) g 2
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
        (connectionDifferenceEndomorphism (I := I) (M := M) g gmU)) ≤
      (fr * Ba R * A) ^ 2 :=
    harmU gmU Q hQsymm hQtie hδ_le hδ0 hδQ hδZ R A hR hA hQ2 hQ3
  have hJhatD : covariantJetNormSq (I := I) (M := M) g 1
      (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmT -
        connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmU) ≤
      (B0ω R * D2 + B1ω R * A * D2) ^ 2 := by
    rw [hat_eq_lip (I := I) (M := M) g gmT,
      hat_eq_lip (I := I) (M := M) g gmU]
    exact hω gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδQ hδZ R A D2 hR hA hD2 hP2 hQ2 hP3 hPQ2
  have hJarmD : covariantJetNormSq (I := I) (M := M) g 1
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gmT) -
        bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gmU)) ≤
      (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 :=
    harmD gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδ_le hδ0 hδQ R A D2 hR hA hD2 hQ2 hP3 hPQ2
  have hJhatP : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmT) ≤
      (Bh R * A) ^ 2 :=
    hhatb gmT P hPsymm hPtie hδ_le hδ0 hδP hδZ R A hR hA hP2 hP3
  have hp1 : covariantJetNormSq (I := I) (M := M) g 2
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gmU)) *
      covariantJetNormSq (I := I) (M := M) g 1
        (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmT -
          connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmU) ≤
      (fr * Ba R * A) ^ 2 * (B0ω R * D2 + B1ω R * A * D2) ^ 2 :=
    mul_le_mul hJarmQ hJhatD
      (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
      (sq_nonneg _)
  have hp2 : covariantJetNormSq (I := I) (M := M) g 1
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gmT) -
          bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gmU)) *
      covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmT) ≤
      (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 * (Bh R * A) ^ 2 :=
    mul_le_mul hJarmD hJhatP
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
      (sq_nonneg _)
  have hr4le : covariantJetNormSq (I := I) (M := M) g 1
      (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
        deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s) ≤
      Cr * (D2 ^ 2 +
        ((fr * Ba R * A) ^ 2 * (B0ω R * D2 + B1ω R * A * D2) ^ 2 +
          (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 *
            (Bh R * A) ^ 2)) := by
    refine hr4.trans (mul_le_mul_of_nonneg_left ?_ hCr)
    exact add_le_add hTU2 (add_le_add hp1 hp2)
  have hb1 : (1 : ℝ) ≤ 1 + A + A ^ 2 := by
    calc
      (1 : ℝ) ≤ 1 + A := le_add_of_nonneg_right hA
      _ ≤ 1 + A + A ^ 2 := le_add_of_nonneg_right (sq_nonneg A)
  have hb24 : (1 + A + A ^ 2) ^ 2 ≤ (1 + A + A ^ 2) ^ 4 :=
    pow_le_pow_right₀ hb1 (by norm_num)
  have hbA2 : A ^ 2 ≤ (1 + A + A ^ 2) ^ 2 :=
    sq_le_one_add_add_sq_sq hA
  set pl : ℝ := (1 + A + A ^ 2) ^ 4 with hpl
  have hpl1 : (1 : ℝ) ≤ pl := by
    rw [hpl]
    calc (1 : ℝ) = 1 ^ 4 := by norm_num
      _ ≤ (1 + A + A ^ 2) ^ 4 :=
        pow_le_pow_left₀ zero_le_one hb1 4
  have hplA2 : A ^ 2 ≤ pl := by
    rw [hpl]
    exact hbA2.trans hb24
  have hplA4 : A ^ 4 ≤ pl := by
    rw [hpl]
    calc A ^ 4 = (A ^ 2) ^ 2 := by ring
      _ ≤ ((1 + A + A ^ 2) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg A) hbA2 2
      _ = (1 + A + A ^ 2) ^ 4 := by ring
  have hpl0 : 0 ≤ pl := le_trans zero_le_one hpl1
  have hq1 : (B0ω R * D2 + B1ω R * A * D2) ^ 2 ≤
      (2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2 * A ^ 2) * D2 ^ 2 := by
    calc
      (B0ω R * D2 + B1ω R * A * D2) ^ 2 ≤
          2 * (B0ω R * D2) ^ 2 + 2 * (B1ω R * A * D2) ^ 2 :=
        add_sq_le_two_sq _ _
      _ = (2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2 * A ^ 2) * D2 ^ 2 := by
        ring
  have hq2 : (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 ≤
      (2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2 * A ^ 2) *
        D2 ^ 2 := by
    calc
      (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 ≤
          2 * (fr * B0c R * D2) ^ 2 +
            2 * (fr * B1c R * A * D2) ^ 2 := add_sq_le_two_sq _ _
      _ = (2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2 * A ^ 2) *
          D2 ^ 2 := by
        ring
  have hD22 : 0 ≤ D2 ^ 2 := sq_nonneg _
  have hterm1 : (fr * Ba R * A) ^ 2 *
      (B0ω R * D2 + B1ω R * A * D2) ^ 2 ≤
      (fr * Ba R) ^ 2 * (2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2) *
        (pl * D2 ^ 2) := by
    have h1 : (fr * Ba R * A) ^ 2 *
        (B0ω R * D2 + B1ω R * A * D2) ^ 2 ≤
        (fr * Ba R * A) ^ 2 *
          ((2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2 * A ^ 2) * D2 ^ 2) :=
      mul_le_mul_of_nonneg_left hq1 (sq_nonneg _)
    have h2 : (fr * Ba R * A) ^ 2 *
        ((2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2 * A ^ 2) * D2 ^ 2) =
        (fr * Ba R) ^ 2 *
          (2 * (B0ω R) ^ 2 * A ^ 2 + 2 * (B1ω R) ^ 2 * A ^ 4) *
            D2 ^ 2 := by ring
    have h3 : (fr * Ba R) ^ 2 *
        (2 * (B0ω R) ^ 2 * A ^ 2 + 2 * (B1ω R) ^ 2 * A ^ 4) *
          D2 ^ 2 ≤
        (fr * Ba R) ^ 2 *
          (2 * (B0ω R) ^ 2 * pl + 2 * (B1ω R) ^ 2 * pl) * D2 ^ 2 := by
      have hin : 2 * (B0ω R) ^ 2 * A ^ 2 + 2 * (B1ω R) ^ 2 * A ^ 4 ≤
          2 * (B0ω R) ^ 2 * pl + 2 * (B1ω R) ^ 2 * pl := by
        have i1 : 2 * (B0ω R) ^ 2 * A ^ 2 ≤ 2 * (B0ω R) ^ 2 * pl :=
          mul_le_mul_of_nonneg_left hplA2 (by positivity)
        have i2 : 2 * (B1ω R) ^ 2 * A ^ 4 ≤ 2 * (B1ω R) ^ 2 * pl :=
          mul_le_mul_of_nonneg_left hplA4 (by positivity)
        exact add_le_add i1 i2
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hin (sq_nonneg _)) hD22
    calc (fr * Ba R * A) ^ 2 *
        (B0ω R * D2 + B1ω R * A * D2) ^ 2 ≤
        (fr * Ba R * A) ^ 2 *
          ((2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2 * A ^ 2) * D2 ^ 2) := h1
      _ = (fr * Ba R) ^ 2 *
          (2 * (B0ω R) ^ 2 * A ^ 2 + 2 * (B1ω R) ^ 2 * A ^ 4) *
            D2 ^ 2 := h2
      _ ≤ (fr * Ba R) ^ 2 *
          (2 * (B0ω R) ^ 2 * pl + 2 * (B1ω R) ^ 2 * pl) * D2 ^ 2 := h3
      _ = (fr * Ba R) ^ 2 * (2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2) *
          (pl * D2 ^ 2) := by ring
  have hterm2 : (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 *
      (Bh R * A) ^ 2 ≤
      (2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2) * (Bh R) ^ 2 *
        (pl * D2 ^ 2) := by
    have h1 : (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 *
        (Bh R * A) ^ 2 ≤
        ((2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2 * A ^ 2) *
          D2 ^ 2) * (Bh R * A) ^ 2 :=
      mul_le_mul_of_nonneg_right hq2 (sq_nonneg _)
    have h2 : ((2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2 * A ^ 2) *
        D2 ^ 2) * (Bh R * A) ^ 2 =
        (2 * (fr * B0c R) ^ 2 * A ^ 2 +
          2 * (fr * B1c R) ^ 2 * A ^ 4) * (Bh R) ^ 2 * D2 ^ 2 := by
      ring
    have h3 : (2 * (fr * B0c R) ^ 2 * A ^ 2 +
        2 * (fr * B1c R) ^ 2 * A ^ 4) * (Bh R) ^ 2 * D2 ^ 2 ≤
        (2 * (fr * B0c R) ^ 2 * pl + 2 * (fr * B1c R) ^ 2 * pl) *
          (Bh R) ^ 2 * D2 ^ 2 := by
      have hin : 2 * (fr * B0c R) ^ 2 * A ^ 2 +
          2 * (fr * B1c R) ^ 2 * A ^ 4 ≤
          2 * (fr * B0c R) ^ 2 * pl + 2 * (fr * B1c R) ^ 2 * pl := by
        have i1 : 2 * (fr * B0c R) ^ 2 * A ^ 2 ≤
            2 * (fr * B0c R) ^ 2 * pl :=
          mul_le_mul_of_nonneg_left hplA2 (by positivity)
        have i2 : 2 * (fr * B1c R) ^ 2 * A ^ 4 ≤
            2 * (fr * B1c R) ^ 2 * pl :=
          mul_le_mul_of_nonneg_left hplA4 (by positivity)
        exact add_le_add i1 i2
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hin (sq_nonneg _)) hD22
    calc (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 *
        (Bh R * A) ^ 2 ≤
        ((2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2 * A ^ 2) *
          D2 ^ 2) * (Bh R * A) ^ 2 := h1
      _ = (2 * (fr * B0c R) ^ 2 * A ^ 2 +
          2 * (fr * B1c R) ^ 2 * A ^ 4) * (Bh R) ^ 2 * D2 ^ 2 := h2
      _ ≤ (2 * (fr * B0c R) ^ 2 * pl + 2 * (fr * B1c R) ^ 2 * pl) *
          (Bh R) ^ 2 * D2 ^ 2 := h3
      _ = (2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2) * (Bh R) ^ 2 *
          (pl * D2 ^ 2) := by ring
  have hD2pl : D2 ^ 2 ≤ pl * D2 ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hpl1 hD22
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
          rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) ≤
      fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 1
        (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
          deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s) := hXle
    _ ≤ fr ^ 2 * (Cr * (D2 ^ 2 +
        ((fr * Ba R * A) ^ 2 * (B0ω R * D2 + B1ω R * A * D2) ^ 2 +
          (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 *
            (Bh R) ^ 2 * A ^ 2))) := by
      refine mul_le_mul_of_nonneg_left ?_ hfr2
      refine hr4le.trans (le_of_eq ?_)
      ring
    _ ≤ fr ^ 2 * (Cr *
        ((1 + (fr * Ba R) ^ 2 * (2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2) +
          (2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2) * (Bh R) ^ 2) *
            (pl * D2 ^ 2))) := by
      refine mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ?_ hCr) hfr2
      have hterm2' : (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 *
          (Bh R) ^ 2 * A ^ 2 ≤
          (2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2) * (Bh R) ^ 2 *
            (pl * D2 ^ 2) := by
        have heq : (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 *
            (Bh R) ^ 2 * A ^ 2 =
            (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 *
              (Bh R * A) ^ 2 := by ring
        rw [heq]
        exact hterm2
      have hsum : D2 ^ 2 +
          ((fr * Ba R * A) ^ 2 * (B0ω R * D2 + B1ω R * A * D2) ^ 2 +
            (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 *
              (Bh R) ^ 2 * A ^ 2) ≤
          pl * D2 ^ 2 +
            ((fr * Ba R) ^ 2 * (2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2) *
                (pl * D2 ^ 2) +
              (2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2) *
                (Bh R) ^ 2 * (pl * D2 ^ 2)) := by
        exact add_le_add hD2pl (add_le_add hterm1 hterm2')
      refine hsum.trans (le_of_eq ?_)
      ring
    _ = C R * ((1 + A + A ^ 2) ^ 4 * D2 ^ 2) := by
      simp only [C, hpl]
      ring

private theorem lieCov_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 N : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 1
          ((deTurckLieCovariantDerivativeTermField (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδT hδZ
              lieDecompositionQ lieDecompositionEps s) -
          (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g U hδU hδZ
              lieDecompositionQ lieDecompositionEps s)) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
  obtain ⟨C₂, hC₂, happ⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 2 6 2
  obtain ⟨ρp, Cp, hρp, hCp, hlcvp⟩ :=
    lcvPair_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Bp, hρb, hBp, hlcvb⟩ :=
    lcvPair_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨Dr, hDr, hcovb⟩ :=
    covX_bdd_h1 (I := I) (M := M) hDim g
  obtain ⟨Cx, hCx, hcovp⟩ :=
    covX_pair_h1 (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  let B : ℝ → ℝ := fun R =>
    2 * (C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) + C₂ * Bp * Cx R)
  refine ⟨min ρp ρb, B, lt_min hρp hρb, ?_, ?_⟩
  · intro R hR
    have h1 : 0 ≤ C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) := by positivity
    have h2 : 0 ≤ C₂ * Bp * Cx R :=
      mul_nonneg (mul_nonneg hC₂ hBp) (hCx R hR)
    exact mul_nonneg (by norm_num) (add_nonneg h1 h2)
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem
        (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem
        (I := I) g U 0 hδU hδZ hs_mem x u v
  have hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρp := by
    rw [hcP, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTn.trans (min_le_left _ _))
  have hQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρp := by
    rw [hcQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hUn.trans (min_le_left _ _))
  have hQnb : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρb := by
    rw [hcQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hUn.trans (min_le_right _ _))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤
      N := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  have hUT :
      deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gmT g -
        deTurckLieCovariantDerivativeDecompositionPairTraceFamily (I := I) (M := M)
          g T hδT hδZ
            ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
              Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                Equiv.swap (0 : Fin 4) 1,
              Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
            ![(-1 : ℝ), -1, 1] s =
      (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) := by
    rw [hgmT]
    exact lieCov_residual (I := I) (M := M) g T hδ_lt hδT hδZ hT hs
  have hUU :
      deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gmU g -
        deTurckLieCovariantDerivativeDecompositionPairTraceFamily (I := I) (M := M)
          g U hδU hδZ
            ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
              Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                Equiv.swap (0 : Fin 4) 1,
              Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
            ![(-1 : ℝ), -1, 1] s =
      (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) := by
    rw [hgmU]
    exact lieCov_residual (I := I) (M := M) g U hδ_lt hδU hδZ hU hs
  rw [edgePair_eq_lip (I := I) (M := M) g T hδT hδZ s,
    edgePair_eq_lip (I := I) (M := M) g U hδU hδZ s, hUT, hUU]
  have htel :
      (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) -
        (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) =
      (-1 : ℝ) • (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT -
            cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) +
        ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
            rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)))) := by
    rw [operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
    module
  rw [htel, jet_smul_lip]
  rw [neg_one_sq, one_mul]
  have hPairD : covariantJetNormSq (I := I) (M := M) g 2
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT -
        cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU) ≤ (Cp * N) ^ 2 := by
    refine (hlcvp P Q gmT gmU hPtie hQtie hPn hQn).trans ?_
    have h1 : Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖ ≤ Cp * N :=
      mul_le_mul_of_nonneg_left hPQn hCp
    exact pow_le_pow_left₀
      (mul_nonneg hCp (norm_nonneg _)) h1 2
  have hPairU : covariantJetNormSq (I := I) (M := M) g 2
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU) ≤ Bp :=
    hlcvb Q gmU hQtie hQnb
  have hXT : covariantJetNormSq (I := I) (M := M) g 1
      (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
        (slotExtendIter (I := I) (M := M) g 0 4 2
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) ≤
      fr ^ 2 * (Dr R * (A + A ^ 2)) ^ 2 :=
    hcovb T hT hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hs
  have hXD : covariantJetNormSq (I := I) (M := M) g 1
      (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
        rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) ≤
      Cx R * ((1 + A + A ^ 2) ^ 4 * D2 ^ 2) :=
    hcovp T U hT hU hδ_le hδ0 hδT hδU hδZ
      R A D2 hR hA hD2 hT2 hU2 hT3 hU3 hTU2 hs
  have happ1 := happ
    (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT -
      cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
    (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
      (slotExtendIter (I := I) (M := M) g 0 4 2
        (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)))
  have happ2 := happ
    (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
    (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
        (slotExtendIter (I := I) (M := M) g 0 4 2
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
      rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
        (slotExtendIter (I := I) (M := M) g 0 4 2
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)))
  have hb1 : (1 : ℝ) ≤ 1 + A + A ^ 2 := by
    calc
      (1 : ℝ) ≤ 1 + A := le_add_of_nonneg_right hA
      _ ≤ 1 + A + A ^ 2 := le_add_of_nonneg_right (sq_nonneg A)
  have hbAA : (A + A ^ 2) ^ 2 ≤ (1 + A + A ^ 2) ^ 4 := by
    have h1 : A + A ^ 2 ≤ (1 + A + A ^ 2) ^ 2 :=
      add_sq_le_one_add_add_sq_sq hA
    have h0 : (0 : ℝ) ≤ A + A ^ 2 := by positivity
    calc (A + A ^ 2) ^ 2 ≤ ((1 + A + A ^ 2) ^ 2) ^ 2 :=
        pow_le_pow_left₀ h0 h1 2
      _ = (1 + A + A ^ 2) ^ 4 := by ring
  have hpl0 : (0 : ℝ) ≤ (1 + A + A ^ 2) ^ 4 := by positivity
  have hT1 : covariantJetNormSq (I := I) (M := M) g 1
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT -
          cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)))) ≤
      C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) *
        ((1 + A + A ^ 2) ^ 4 * N ^ 2) := by
    refine happ1.trans ?_
    have hstep : C₂ * covariantJetNormSq (I := I) (M := M) g 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT -
          cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU) *
        covariantJetNormSq (I := I) (M := M) g 1
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) ≤
        C₂ * (Cp * N) ^ 2 * (fr ^ 2 * (Dr R * (A + A ^ 2)) ^ 2) := by
      refine mul_le_mul ?_ hXT
        (jet_nonneg_lip (I := I) (M := M) (m := 1) g _) ?_
      · exact mul_le_mul_of_nonneg_left hPairD hC₂
      · exact mul_nonneg hC₂ (sq_nonneg _)
    refine hstep.trans ?_
    have hAA : (Dr R * (A + A ^ 2)) ^ 2 =
        (Dr R) ^ 2 * (A + A ^ 2) ^ 2 := by ring
    have hmono : (Dr R) ^ 2 * (A + A ^ 2) ^ 2 ≤
        (Dr R) ^ 2 * (1 + A + A ^ 2) ^ 4 :=
      mul_le_mul_of_nonneg_left hbAA (sq_nonneg _)
    calc C₂ * (Cp * N) ^ 2 * (fr ^ 2 * (Dr R * (A + A ^ 2)) ^ 2) =
        C₂ * Cp ^ 2 * (fr ^ 2 * ((Dr R) ^ 2 * (A + A ^ 2) ^ 2)) *
          N ^ 2 := by ring
      _ ≤ C₂ * Cp ^ 2 * (fr ^ 2 * ((Dr R) ^ 2 *
          (1 + A + A ^ 2) ^ 4)) * N ^ 2 := by
        have hin : fr ^ 2 * ((Dr R) ^ 2 * (A + A ^ 2) ^ 2) ≤
            fr ^ 2 * ((Dr R) ^ 2 * (1 + A + A ^ 2) ^ 4) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hbAA (sq_nonneg _))
            (sq_nonneg _)
        have hout : C₂ * Cp ^ 2 * (fr ^ 2 * ((Dr R) ^ 2 *
            (A + A ^ 2) ^ 2)) ≤
            C₂ * Cp ^ 2 * (fr ^ 2 * ((Dr R) ^ 2 *
              (1 + A + A ^ 2) ^ 4)) :=
          mul_le_mul_of_nonneg_left hin
            (mul_nonneg hC₂ (sq_nonneg _))
        exact mul_le_mul_of_nonneg_right hout (sq_nonneg _)
      _ = C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) *
          ((1 + A + A ^ 2) ^ 4 * N ^ 2) := by ring
  have hT2b : covariantJetNormSq (I := I) (M := M) g 1
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
          rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)))) ≤
      C₂ * Bp * Cx R * ((1 + A + A ^ 2) ^ 4 * D2 ^ 2) := by
    refine happ2.trans ?_
    have hstep : C₂ * covariantJetNormSq (I := I) (M := M) g 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU) *
        covariantJetNormSq (I := I) (M := M) g 1
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
            rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) ≤
        C₂ * Bp * (Cx R * ((1 + A + A ^ 2) ^ 4 * D2 ^ 2)) := by
      refine mul_le_mul ?_ hXD
        (jet_nonneg_lip (I := I) (M := M) (m := 1) g _) ?_
      · exact mul_le_mul_of_nonneg_left hPairU hC₂
      · exact mul_nonneg hC₂ hBp
    refine hstep.trans (le_of_eq ?_)
    ring
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
            (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT -
              cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
            (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) +
          ccOperatorFieldComp (I := I) (M := M) g 2 6 2
            (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
            (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
                (slotExtendIter (I := I) (M := M) g 0 4 2
                  (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
              rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
                (slotExtendIter (I := I) (M := M) g 0 4 2
                  (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)))) ≤
      2 * (covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
            (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT -
              cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
            (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)))) +
        covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
            (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
            (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
                (slotExtendIter (I := I) (M := M) g 0 4 2
                  (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
              rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
                (slotExtendIter (I := I) (M := M) g 0 4 2
                  (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))))) :=
      jet_add_lip (I := I) (M := M) g 1 _ _
    _ ≤ 2 * (C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) *
          ((1 + A + A ^ 2) ^ 4 * N ^ 2) +
        C₂ * Bp * Cx R * ((1 + A + A ^ 2) ^ 4 * D2 ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hT1 hT2b) (by norm_num)
    _ ≤ B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
      have c1 : (0 : ℝ) ≤ C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) := by
        positivity
      have c2 : (0 : ℝ) ≤ C₂ * Bp * Cx R :=
        mul_nonneg (mul_nonneg hC₂ hBp) (hCx R hR)
      have hd : (0 : ℝ) ≤ (1 + A + A ^ 2) ^ 4 * D2 ^ 2 :=
        mul_nonneg hpl0 (sq_nonneg _)
      have hn : (0 : ℝ) ≤ (1 + A + A ^ 2) ^ 4 * N ^ 2 :=
        mul_nonneg hpl0 (sq_nonneg _)
      have hsum : 2 * (C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) *
            ((1 + A + A ^ 2) ^ 4 * N ^ 2) +
          C₂ * Bp * Cx R * ((1 + A + A ^ 2) ^ 4 * D2 ^ 2)) ≤
          2 * (C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) *
              ((1 + A + A ^ 2) ^ 4 * D2 ^ 2 +
                (1 + A + A ^ 2) ^ 4 * N ^ 2) +
            C₂ * Bp * Cx R *
              ((1 + A + A ^ 2) ^ 4 * D2 ^ 2 +
                (1 + A + A ^ 2) ^ 4 * N ^ 2)) := by
        have e1 : C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) *
            ((1 + A + A ^ 2) ^ 4 * N ^ 2) ≤
            C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) *
              ((1 + A + A ^ 2) ^ 4 * D2 ^ 2 +
                (1 + A + A ^ 2) ^ 4 * N ^ 2) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hd) c1
        have e2 : C₂ * Bp * Cx R *
            ((1 + A + A ^ 2) ^ 4 * D2 ^ 2) ≤
            C₂ * Bp * Cx R *
              ((1 + A + A ^ 2) ^ 4 * D2 ^ 2 +
                (1 + A + A ^ 2) ^ 4 * N ^ 2) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hn) c2
        exact mul_le_mul_of_nonneg_left (add_le_add e1 e2) (by norm_num)
      refine hsum.trans (le_of_eq ?_)
      simp only [B]
      ring

private theorem ipLowCc_bounds_lip
    (g : SmoothRiemannianMetric I M)
    (C1 C2 J Wb Wm p u : ℝ)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hJ : 0 ≤ J)
    (WT WU : SmoothCcTensor g 0 1)
    (happ1 : ∀ (Φ : SmoothCcTensor g 3 1) (W : SmoothCcTensor g 2 3),
      covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g 2 3 1 Φ W) ≤
        C1 * covariantJetNormSq (I := I) (M := M) g 2 Φ *
          covariantJetNormSq (I := I) (M := M) g 1 W)
    (happ2 : ∀ (Φ : SmoothCcTensor g 3 1) (W : SmoothCcTensor g 2 3),
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 2 3 1 Φ W) ≤
        C2 * covariantJetNormSq (I := I) (M := M) g 2 Φ *
          covariantJetNormSq (I := I) (M := M) g 2 W)
    (hJdef : covariantJetNormSq (I := I) (M := M) g 2
      (ipLowCoeff (I := I) (M := M) g) = J)
    (hWT : covariantJetNormSq (I := I) (M := M) g 2 WT ≤ Wb * p)
    (hWd : covariantJetNormSq (I := I) (M := M) g 1 (WT - WU) ≤ Wm * (p * u)) :
    covariantJetNormSq (I := I) (M := M) g 2 (ipLowCc (I := I) (M := M) g WT) ≤
        (C2 * J * (Module.finrank ℝ E : ℝ) ^ 2 * Wb) * p ∧
      covariantJetNormSq (I := I) (M := M) g 1 (ipLowCc (I := I) (M := M) g WT) ≤
        (C2 * J * (Module.finrank ℝ E : ℝ) ^ 2 * Wb) * p ∧
      covariantJetNormSq (I := I) (M := M) g 1
        (ipLowCc (I := I) (M := M) g WT - ipLowCc (I := I) (M := M) g WU) ≤
        (C1 * J * (Module.finrank ℝ E : ℝ) ^ 2 * Wm) * (p * u) := by
  let fr : ℝ := Module.finrank ℝ E
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hIp2 : covariantJetNormSq (I := I) (M := M) g 2
      (ipLowCc (I := I) (M := M) g WT) ≤ (C2 * J * fr ^ 2 * Wb) * p := by
    rw [ipLowCc_eq_ccOperatorFieldComp]
    refine (happ2 (ipLowCoeff (I := I) (M := M) g) _).trans ?_
    have hslot : covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 2
          (slotExtend (I := I) (M := M) g 0 1 WT)) ≤
        fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 WT) :=
      le_trans (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 2 _)
        (mul_le_mul_of_nonneg_left (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 1 _) hfr)
    calc
      C2 * covariantJetNormSq (I := I) (M := M) g 2 (ipLowCoeff (I := I) (M := M) g) *
          covariantJetNormSq (I := I) (M := M) g 2
            (slotExtend (I := I) (M := M) g 1 2
              (slotExtend (I := I) (M := M) g 0 1 WT)) ≤
          C2 * J * (fr * (fr * (Wb * p))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (le_of_eq hJdef) hC2)
          (le_trans hslot
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hWT hfr) hfr))
          (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hC2 hJ)
      _ = (C2 * J * fr ^ 2 * Wb) * p := by ring
  refine ⟨hIp2, le_trans (jet_mono_lip (I := I) (M := M) g (by norm_num) _) hIp2, ?_⟩
  rw [← ipLowCc_sub, ipLowCc_eq_ccOperatorFieldComp]
  refine (happ1 (ipLowCoeff (I := I) (M := M) g) _).trans ?_
  have hslot : covariantJetNormSq (I := I) (M := M) g 1
      (slotExtend (I := I) (M := M) g 1 2
        (slotExtend (I := I) (M := M) g 0 1 (WT - WU))) ≤
      fr * (fr * covariantJetNormSq (I := I) (M := M) g 1 (WT - WU)) :=
    le_trans (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 2 _)
      (mul_le_mul_of_nonneg_left (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 1 _) hfr)
  calc
    C1 * covariantJetNormSq (I := I) (M := M) g 2 (ipLowCoeff (I := I) (M := M) g) *
        covariantJetNormSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 1 2
            (slotExtend (I := I) (M := M) g 0 1 (WT - WU))) ≤
        C1 * J * (fr * (fr * (Wm * (p * u)))) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left (le_of_eq hJdef) hC1)
        (le_trans hslot
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hWd hfr) hfr))
        (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
        (mul_nonneg hC1 hJ)
    _ = (C1 * J * fr ^ 2 * Wm) * (p * u) := by ring

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma vb_rank0_smul_lip (x : M) (c : Tensor0SSpace 0 I x) :
    c = Tensor0SSpace.toModel c (fun i : Fin 0 => i.elim0) •
      unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, smul_apply,
    smul_eq_mul]
  have h1 : Tensor0SSpace.toModel
      (unitTensor (I := I) (M := M) x) v = (1 : ℝ) := rfl
  rw [h1, mul_one]
  congr 1
  funext i
  exact i.elim0

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma vbMcd_unit_lip (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀) x
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (m i)) =
      g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E)
          (E := (TangentSpace I : M → Type _)) x).smulRight
        (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact metricConnectionDifferenceLoweredFib_toModel (I := I) g₁ g₁ g₀ x m

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma vbPK_slotExt_lip (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (B : Tensor0SSpace 1 I x) :
    Tensor0SSpace.toModel
        (tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
          (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x) B) =
      Tensor0SSpace.toModel
        (DifferentialGeometry.Integral.Connection.slotExtendFib
          (I := I) (M := M) 0 3 x
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀).toSection x)
          B) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro u
  rw [show (u : Fin 4 → E) = Fin.cons (u 0) (Fin.tail u) from
    (Fin.cons_self_tail u).symm]
  rw [tensor0SProdKappaFib_apply, Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  rw [DifferentialGeometry.Integral.Connection.slotExtendFib_apply_eval
    (I := I) (M := M) 0 3 x
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀).toSection x)
    B (u 0) (Fin.tail u)]
  have hc : tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 0 x B
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (u 0)) =
      Tensor0SSpace.toModel B (fun _ : Fin 1 => u 0) •
        unitTensor (I := I) (M := M) x := by
    have h2 := vb_rank0_smul_lip (I := I) (M := M) x
      (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 0 x B
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (u 0)))
    rw [h2]
    congr 1
    rw [TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M)
      (T := B) (v0 := u 0) (vs := fun i : Fin 0 => i.elim0)]
    congr 1
    funext k
    fin_cases k
    rfl
  rw [hc, ContinuousLinearMap.map_smul, Tensor0SSpace.toModel_smul,
    smul_apply, smul_eq_mul]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀).toSection x)
        (unitTensor (I := I) (M := M) x)) (Fin.tail u) =
      unitModel (I := I) (M := M) g₀ 3
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀) x
        (fun j => Fin.tail u j) from by rw [unitModel]]
  have hm : (fun j => Fin.tail u j) =
      fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (Fin.tail u j)) := by
    funext j
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [hm, vbMcd_unit_lip (I := I) (M := M) g₀ g₁ x
    (fun j => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (Fin.tail u j))]
  have hcast : ((Fin.cons (u 0) (Fin.tail u) : Fin 4 → E) ∘
      Fin.castAdd 3) = (fun _ : Fin 1 => u 0) := by
    funext i
    fin_cases i
    rfl
  have hnat : ((Fin.cons (u 0) (Fin.tail u) : Fin 4 → E) ∘
      Fin.natAdd 1) = Fin.tail u := by
    funext j
    have hj : Fin.natAdd 1 j = Fin.succ j := by
      apply Fin.ext
      simp [Fin.natAdd, Fin.succ, Nat.add_comm]
    change Fin.cons (u 0) (Fin.tail u) (Fin.natAdd 1 j) = Fin.tail u j
    rw [hj, Fin.cons_succ]
  rw [hcast, hnat]
  rw [metricConnectionDifferenceLoweredFib_toModel (I := I) g₁ g₁ g₀ x
    (fun j => Fin.tail u j)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma vbmcd_rel_lip (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∀ (y : M) (d : Tensor0SSpace 1 I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 4 I y from
            (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁).toSection y) d) =
        ContinuousMultilinearMap.domDomCongr LieCorrectionZeroFiberOperators.lieCorrectionZeroVectorBundleTracePermutation
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 4 I y from
              (slotExtend (I := I) (M := M) g₀ 0 3
                (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀)).toSection
                  y) d)) := by
  intro y d
  rw [show ((show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 4 I y from
      (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁).toSection y) d) =
      domDomCongrFibRank (I := I) 4 LieCorrectionZeroFiberOperators.lieCorrectionZeroVectorBundleTracePermutation y
        (tensor0SProdKappaFib (I := I) (p := 1) (q := 3) y
          (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ y) d) from rfl]
  rw [domDomCongrFibRank_apply, Tensor0SSpace.toModel_ofModel]
  exact congrArg
    (ContinuousMultilinearMap.domDomCongr LieCorrectionZeroFiberOperators.lieCorrectionZeroVectorBundleTracePermutation)
    (vbPK_slotExt_lip (I := I) (M := M) g₀ g₁ y d)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem vbmcd_perm_eq
    (g gm : SmoothRiemannianMetric I M) :
    lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gm =
      rsDomDomCongrSection (I := I) (M := M) g 1 4
        LieCorrectionZeroFiberOperators.lieCorrectionZeroVectorBundleTracePermutation
        (slotExtend (I := I) (M := M) g 0 3
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g)) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro d
  apply Tensor0SSpace.toModel_injective
  beta_reduce
  rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]
  exact vbmcd_rel_lip (I := I) (M := M) g gm x d

private theorem vbmcd_h2_lip
    (g gm : SmoothRiemannianMetric I M) :
    covariantJetNormSq (I := I) (M := M) g 2 (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gm) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 2
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g) := by
  rw [vbmcd_perm_eq, covariantJetNormSq_rsDomDomCongrSection]
  exact covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _

private theorem vbmcd_sub_h1_lip
    (g gT gU : SmoothRiemannianMetric I M) :
    covariantJetNormSq (I := I) (M := M) g 1
        (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gT -
          lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gU) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 1
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gT g -
            metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gU g) := by
  rw [vbmcd_perm_eq, vbmcd_perm_eq, ← rsperm_sub_lip, ← slotExtend_sub,
    covariantJetNormSq_rsDomDomCongrSection]
  exact covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _

private theorem vbmcd_bounds_lip
    (g gT gU : SmoothRiemannianMetric I M)
    (bm b0 b1 p u : ℝ)
    (hT : covariantJetNormSq (I := I) (M := M) g 2
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gT g) ≤
        bm ^ 2 * (2 * p))
    (hU : covariantJetNormSq (I := I) (M := M) g 2
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gU g) ≤
        bm ^ 2 * (2 * p))
    (hd : covariantJetNormSq (I := I) (M := M) g 1
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gT g -
        metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gU g) ≤
        (2 * b0 ^ 2 + 2 * b1 ^ 2) * (p * u)) :
    covariantJetNormSq (I := I) (M := M) g 2
        (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gT) ≤
          ((Module.finrank ℝ E : ℝ) * bm ^ 2 * 2) * p ∧
      covariantJetNormSq (I := I) (M := M) g 2
        (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gU) ≤
          ((Module.finrank ℝ E : ℝ) * bm ^ 2 * 2) * p ∧
      covariantJetNormSq (I := I) (M := M) g 1
        (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gT -
          lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gU) ≤
          ((Module.finrank ℝ E : ℝ) *
            (2 * b0 ^ 2 + 2 * b1 ^ 2)) * (p * u) := by
  have hfr : 0 ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  refine ⟨(vbmcd_h2_lip (I := I) (M := M) g gT).trans ?_,
    (vbmcd_h2_lip (I := I) (M := M) g gU).trans ?_,
    (vbmcd_sub_h1_lip (I := I) (M := M) g gT gU).trans ?_⟩
  · exact (mul_le_mul_of_nonneg_left hT hfr).trans_eq (by ring)
  · exact (mul_le_mul_of_nonneg_left hU hfr).trans_eq (by ring)
  · exact (mul_le_mul_of_nonneg_left hd hfr).trans_eq (by ring)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem app_pair_h21_lip
    (g : SmoothRiemannianMetric I M) {p r c : ℕ}
    (C a b d e : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (ΦT ΦU : SmoothCcTensor g r c) (WT WU : SmoothCcTensor g p r)
    (happ : ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
      covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
        C * covariantJetNormSq (I := I) (M := M) g 2 Φ *
          covariantJetNormSq (I := I) (M := M) g 1 W)
    (hΦd : covariantJetNormSq (I := I) (M := M) g 2 (ΦT - ΦU) ≤ a)
    (hWT : covariantJetNormSq (I := I) (M := M) g 1 WT ≤ b)
    (hΦU : covariantJetNormSq (I := I) (M := M) g 2 ΦU ≤ d)
    (hWd : covariantJetNormSq (I := I) (M := M) g 1 (WT - WU) ≤ e) :
    covariantJetNormSq (I := I) (M := M) g 1
        (ccOperatorFieldComp (I := I) (M := M) g p r c ΦT WT -
          ccOperatorFieldComp (I := I) (M := M) g p r c ΦU WU) ≤
      2 * (C * a * b + C * d * e) := by
  have hdel :
      ccOperatorFieldComp (I := I) (M := M) g p r c ΦT WT -
          ccOperatorFieldComp (I := I) (M := M) g p r c ΦU WU =
        ccOperatorFieldComp (I := I) (M := M) g p r c (ΦT - ΦU) WT +
          ccOperatorFieldComp (I := I) (M := M) g p r c ΦU (WT - WU) := by
    rw [operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
    module
  rw [hdel]
  have h1 := (happ (ΦT - ΦU) WT).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hΦd hC) hWT
      (jet_nonneg_lip (I := I) (M := M) (m := 1) g WT)
      (mul_nonneg hC ha))
  have h2 := (happ ΦU (WT - WU)).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hΦU hC) hWd
      (jet_nonneg_lip (I := I) (M := M) (m := 1) g (WT - WU))
      (mul_nonneg hC hd))
  exact (jet_add_lip (I := I) (M := M) g 1 _ _).trans
    (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num))

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem app_pair_h12_h21_lip
    (g : SmoothRiemannianMetric I M) {p r c : ℕ}
    (C12 C21 a b d e : ℝ) (hC12 : 0 ≤ C12) (hC21 : 0 ≤ C21)
    (ha : 0 ≤ a) (hd : 0 ≤ d)
    (ΦT ΦU : SmoothCcTensor g r c) (WT WU : SmoothCcTensor g p r)
    (happ12 : ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
      covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
        C12 * covariantJetNormSq (I := I) (M := M) g 1 Φ *
          covariantJetNormSq (I := I) (M := M) g 2 W)
    (happ21 : ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
      covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
        C21 * covariantJetNormSq (I := I) (M := M) g 2 Φ *
          covariantJetNormSq (I := I) (M := M) g 1 W)
    (hΦd : covariantJetNormSq (I := I) (M := M) g 1 (ΦT - ΦU) ≤ a)
    (hWT : covariantJetNormSq (I := I) (M := M) g 2 WT ≤ b)
    (hΦU : covariantJetNormSq (I := I) (M := M) g 2 ΦU ≤ d)
    (hWd : covariantJetNormSq (I := I) (M := M) g 1 (WT - WU) ≤ e) :
    covariantJetNormSq (I := I) (M := M) g 1
        (ccOperatorFieldComp (I := I) (M := M) g p r c ΦT WT -
          ccOperatorFieldComp (I := I) (M := M) g p r c ΦU WU) ≤
      2 * (C12 * a * b + C21 * d * e) := by
  have hdel :
      ccOperatorFieldComp (I := I) (M := M) g p r c ΦT WT -
          ccOperatorFieldComp (I := I) (M := M) g p r c ΦU WU =
        ccOperatorFieldComp (I := I) (M := M) g p r c (ΦT - ΦU) WT +
          ccOperatorFieldComp (I := I) (M := M) g p r c ΦU (WT - WU) := by
    rw [operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
    module
  rw [hdel]
  have h1 := (happ12 (ΦT - ΦU) WT).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hΦd hC12) hWT
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g WT)
      (mul_nonneg hC12 ha))
  have h2 := (happ21 ΦU (WT - WU)).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hΦU hC21) hWd
      (jet_nonneg_lip (I := I) (M := M) (m := 1) g (WT - WU))
      (mul_nonneg hC21 hd))
  exact (jet_add_lip (I := I) (M := M) g 1 _ _).trans
    (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num))

private theorem vb_w_pair_factor_lip
    (C Ct Bt Bs W0 W1 pl2 u : ℝ) :
    2 * (C * (Ct ^ 2 * u) * (Bs ^ 2 * pl2) +
      C * Bt ^ 2 * ((2 * W0 ^ 2 + 2 * W1 ^ 2) * (pl2 * u))) =
      (2 * (C * Ct ^ 2 * Bs ^ 2 +
        C * Bt ^ 2 * (2 * W0 ^ 2 + 2 * W1 ^ 2))) * (pl2 * u) := by
  ring

private theorem vb_inner_pair_factor_lip
    (C12 C21 Vd Ib Vb Im pl2 u : ℝ) :
    2 * (C12 * (Vd * (pl2 * u)) * (Ib * pl2) +
      C21 * (Vb * pl2) * (Im * (pl2 * u))) =
      2 * ((C12 * Vd * Ib) * ((pl2 * pl2) * u) +
        (C21 * Vb * Im) * ((pl2 * pl2) * u)) := by
  ring

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem vb_inner_bounds_lip
    (g : SmoothRiemannianMetric I M)
    (C12 C21 Vd Ib Vb Im p u : ℝ)
    (hC12 : 0 ≤ C12) (hC21 : 0 ≤ C21)
    (hVd : 0 ≤ Vd) (hVb : 0 ≤ Vb) (hp : 0 ≤ p) (hpu : 0 ≤ p * u)
    (VT VU : SmoothCcTensor g 1 4) (IT IU : SmoothCcTensor g 2 1)
    (happ12 : ∀ (Φ : SmoothCcTensor g 1 4) (W : SmoothCcTensor g 2 1),
      covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g 2 1 4 Φ W) ≤
        C12 * covariantJetNormSq (I := I) (M := M) g 1 Φ *
          covariantJetNormSq (I := I) (M := M) g 2 W)
    (happ21 : ∀ (Φ : SmoothCcTensor g 1 4) (W : SmoothCcTensor g 2 1),
      covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g 2 1 4 Φ W) ≤
        C21 * covariantJetNormSq (I := I) (M := M) g 2 Φ *
          covariantJetNormSq (I := I) (M := M) g 1 W)
    (hVT : covariantJetNormSq (I := I) (M := M) g 2 VT ≤ Vb * p)
    (hVd' : covariantJetNormSq (I := I) (M := M) g 1 (VT - VU) ≤ Vd * (p * u))
    (hIT1 : covariantJetNormSq (I := I) (M := M) g 1 IT ≤ Ib * p)
    (hIT2 : covariantJetNormSq (I := I) (M := M) g 2 IT ≤ Ib * p)
    (hVU : covariantJetNormSq (I := I) (M := M) g 2 VU ≤ Vb * p)
    (hId : covariantJetNormSq (I := I) (M := M) g 1 (IT - IU) ≤ Im * (p * u)) :
    covariantJetNormSq (I := I) (M := M) g 1
        (ccOperatorFieldComp (I := I) (M := M) g 2 1 4 VT IT) ≤
          (C21 * Vb * Ib) * (p * p) ∧
      covariantJetNormSq (I := I) (M := M) g 1
        (ccOperatorFieldComp (I := I) (M := M) g 2 1 4 VT IT -
          ccOperatorFieldComp (I := I) (M := M) g 2 1 4 VU IU) ≤
          2 * ((C12 * Vd * Ib) * ((p * p) * u) +
            (C21 * Vb * Im) * ((p * p) * u)) := by
  constructor
  · refine (happ21 VT IT).trans ?_
    calc
      C21 * covariantJetNormSq (I := I) (M := M) g 2 VT *
          covariantJetNormSq (I := I) (M := M) g 1 IT ≤
          C21 * (Vb * p) * (Ib * p) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hVT hC21) hIT1
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g IT)
          (mul_nonneg hC21 (mul_nonneg hVb hp))
      _ = (C21 * Vb * Ib) * (p * p) := by ring
  · refine (app_pair_h12_h21_lip (I := I) (M := M) g C12 C21
      (Vd * (p * u)) (Ib * p) (Vb * p) (Im * (p * u))
      hC12 hC21 (mul_nonneg hVd hpu) (mul_nonneg hVb hp)
      VT VU IT IU happ12 happ21 hVd' hIT2 hVU hId).trans ?_
    exact le_of_eq (vb_inner_pair_factor_lip C12 C21 Vd Ib Vb Im p u)

private theorem vb_outer_factorization_lip
    (C Ct Bt Sin Kv Ki x d n : ℝ) :
    4 * (2 * (C * (Ct ^ 2 * (d ^ 2 + n ^ 2)) * (Sin * (x ^ 2 * x ^ 2)) +
      C * Bt ^ 2 * (2 *
        (Kv * ((x ^ 2 * x ^ 2) * (d ^ 2 + n ^ 2)) +
          Ki * ((x ^ 2 * x ^ 2) * (d ^ 2 + n ^ 2)))))) =
      (4 * (2 * (C * Ct ^ 2 * Sin + C * Bt ^ 2 * (2 * (Kv + Ki))))) *
        (x ^ 4 * (d ^ 2 + n ^ 2)) := by
  ring

omit [NeZero (Module.finrank ℝ E)] in
private theorem vb_outer_bounds_lip
    (g gT gU : SmoothRiemannianMetric I M)
    (C Ct Bt Sin Kv Ki p u : ℝ)
    (hC : 0 ≤ C) (hu : 0 ≤ u)
    (LvT LvU : SmoothCcTensor g 4 2) (InT InU : SmoothCcTensor g 2 4)
    (happ : ∀ (Φ : SmoothCcTensor g 4 2) (W : SmoothCcTensor g 2 4),
      covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g 2 4 2 Φ W) ≤
        C * covariantJetNormSq (I := I) (M := M) g 2 Φ *
          covariantJetNormSq (I := I) (M := M) g 1 W)
    (hLvd : covariantJetNormSq (I := I) (M := M) g 2 (LvT - LvU) ≤ Ct ^ 2 * u)
    (hInT : covariantJetNormSq (I := I) (M := M) g 1 InT ≤ Sin * (p * p))
    (hLvU : covariantJetNormSq (I := I) (M := M) g 2 LvU ≤ Bt ^ 2)
    (hInd : covariantJetNormSq (I := I) (M := M) g 1 (InT - InU) ≤
      2 * (Kv * ((p * p) * u) + Ki * ((p * p) * u)))
    (hFormT : lieCorrectionZeroVectorBundle (I := I) (M := M) g gT =
      (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 4 2 LvT InT)
    (hFormU : lieCorrectionZeroVectorBundle (I := I) (M := M) g gU =
      (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 4 2 LvU InU) :
    covariantJetNormSq (I := I) (M := M) g 1
        (lieCorrectionZeroVectorBundle (I := I) (M := M) g gT - lieCorrectionZeroVectorBundle (I := I) (M := M) g gU) ≤
      4 * (2 * (C * (Ct ^ 2 * u) * (Sin * (p * p)) +
        C * Bt ^ 2 *
          (2 * (Kv * ((p * p) * u) + Ki * ((p * p) * u))))) := by
  have hdel : lieCorrectionZeroVectorBundle (I := I) (M := M) g gT - lieCorrectionZeroVectorBundle (I := I) (M := M) g gU =
      (2 : ℝ) •
        (ccOperatorFieldComp (I := I) (M := M) g 2 4 2 LvT InT -
          ccOperatorFieldComp (I := I) (M := M) g 2 4 2 LvU InU) := by
    rw [hFormT, hFormU]
    module
  rw [hdel, jet_smul_lip]
  have houter := app_pair_h21_lip (I := I) (M := M) g C
    (Ct ^ 2 * u) (Sin * (p * p)) (Bt ^ 2)
    (2 * (Kv * ((p * p) * u) + Ki * ((p * p) * u)))
    hC (mul_nonneg (sq_nonneg _) hu) (sq_nonneg _)
    LvT LvU InT InU happ hLvd hInT hLvU hInd
  rw [show ((2 : ℝ) ^ 2) = 4 by norm_num]
  exact mul_le_mul_of_nonneg_left houter (by norm_num)

private theorem amix_pair_factor_one_lip
    (C Ct S Bt M pl u : ℝ) :
    2 * (C * (Ct ^ 2 * u) * (S * pl) + C * Bt ^ 2 * (M * (pl * u))) =
      2 * ((C * Ct ^ 2 * S) * (pl * u) +
        (C * Bt ^ 2 * M) * (pl * u)) := by
  ring

private theorem amix_pair_factor_two_lip
    (C Ct S Bt K L pl u : ℝ) :
    2 * (C * (Ct ^ 2 * u) * (S * (pl * pl)) +
      C * Bt ^ 2 * (2 *
        (K * ((pl * pl) * u) + L * ((pl * pl) * u)))) =
      2 * ((C * Ct ^ 2 * S) * ((pl * pl) * u) +
        (C * Bt ^ 2 * (2 * (K + L))) * ((pl * pl) * u)) := by
  ring

private theorem amix_pair_factor_mixed_lip
    (C12 F S C21 G K L pl u : ℝ) :
    2 * (C12 * (F * (pl * u)) * (S * pl) +
      C21 * (G * pl) * (2 * (K * (pl * u) + L * (pl * u)))) =
      2 * ((C12 * F * S) * ((pl * pl) * u) +
        (C21 * G * (2 * (K + L))) * ((pl * pl) * u)) := by
  ring

private theorem amix_factorization_lip
    (K L x d n : ℝ) :
    2 * (K * ((x ^ 2 * x ^ 2) * (d ^ 2 + n ^ 2)) +
      L * ((x ^ 2 * x ^ 2) * (d ^ 2 + n ^ 2))) =
      (2 * (K + L)) * (x ^ 4 * (d ^ 2 + n ^ 2)) := by
  ring

private theorem trace_pair_h2_to_sum_lip
    (g : SmoothRiemannianMetric I M) (p : ℕ)
    (P Q : SmoothCcTensor g 0 2)
    (gP gQ : SmoothRiemannianMetric I M)
    (hPtie : ∀ (y : M) (v w : TangentSpace I y),
      gP.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g P y v w)
    (hQtie : ∀ (y : M) (v w : TangentSpace I y),
      gQ.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g Q y v w)
    (ρ Cp D2 N : ℝ)
    (hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ)
    (hQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ)
    (hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N)
    (hCp : 0 ≤ Cp)
    (hpair : ∀ (T U : SmoothCcTensor g 0 2)
      (gT gU : SmoothRiemannianMetric I M),
      (∀ (y : M) (v w : TangentSpace I y),
        gT.inner y v w =
          g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
      (∀ (y : M) (v w : TangentSpace I y),
        gU.inner y v w =
          g.inner y v w + ccTensorBilinSymm (I := I) g U y v w) →
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gT p -
            pureTrace (I := I) (M := M) g gU p) ≤
        (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖) ^ 2) :
    covariantJetNormSq (I := I) (M := M) g 2
        (pureTrace (I := I) (M := M) g gP p -
          pureTrace (I := I) (M := M) g gQ p) ≤
      Cp ^ 2 * (D2 ^ 2 + N ^ 2) := by
  refine (hpair P Q gP gQ hPtie hQtie hPn hQn).trans ?_
  have h1 : Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤
      Cp * N := mul_le_mul_of_nonneg_left hPQn hCp
  refine (pow_le_pow_left₀ (mul_nonneg hCp (norm_nonneg _)) h1 2).trans ?_
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_left (sq_nonneg D2)) (sq_nonneg Cp)

private theorem trace_pair_h2_bdd_lip
    (g : SmoothRiemannianMetric I M) (p : ℕ)
    (P Q : SmoothCcTensor g 0 2)
    (gP gQ : SmoothRiemannianMetric I M)
    (hPtie : ∀ (y : M) (v w : TangentSpace I y),
      gP.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g P y v w)
    (hQtie : ∀ (y : M) (v w : TangentSpace I y),
      gQ.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g Q y v w)
    (ρ Bp : ℝ)
    (hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ)
    (hQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ)
    (hbdd : ∀ (T : SmoothCcTensor g 0 2)
      (gT : SmoothRiemannianMetric I M),
      (∀ (y : M) (v w : TangentSpace I y),
        gT.inner y v w =
          g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gT p) ≤ Bp ^ 2) :
    covariantJetNormSq (I := I) (M := M) g 2
        (pureTrace (I := I) (M := M) g gP p) ≤ Bp ^ 2 ∧
      covariantJetNormSq (I := I) (M := M) g 2
        (pureTrace (I := I) (M := M) g gQ p) ≤ Bp ^ 2 :=
  ⟨hbdd P gP hPtie hPn, hbdd Q gQ hQtie hQn⟩

private theorem vb_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 N : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 1
          (lieCorrectionZeroVectorBundle (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) -
            lieCorrectionZeroVectorBundle (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s)) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
  obtain ⟨Cout, hCout, happOut⟩ := app_h21_mul_lip (I := I) (M := M) hDim g 2 4 2
  obtain ⟨Cin1, hCin1, happIn1⟩ := app_h21_mul_lip (I := I) (M := M) hDim g 2 1 4
  obtain ⟨Cin12, hCin12, happIn12⟩ := app_h12_mul_lip (I := I) (M := M) hDim g 2 1 4
  obtain ⟨Cip1, hCip1, happIp1⟩ := app_h21_mul_lip (I := I) (M := M) hDim g 2 3 1
  obtain ⟨Cip2, hCip2, happIp2⟩ := app_h2_mul_lip (I := I) (M := M) hDim g 2 3 1
  obtain ⟨Cw1, hCw1, happW1⟩ := app_h21_mul_lip (I := I) (M := M) hDim g 0 3 1
  obtain ⟨Cw2, hCw2, happW2⟩ := app_h2_mul_lip (I := I) (M := M) hDim g 0 3 1
  obtain ⟨ρt1, Ct1, hρt1, hCt1, htp1⟩ :=
    RicciDeTurckLowOrder.trace1_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb1, Bt1, hρb1, hBt1, htb1⟩ :=
    RicciDeTurckLowOrder.trace_one_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρt2, Ct2, hρt2, hCt2, htp2⟩ :=
    RicciDeTurckLowOrder.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb2, Bt2, hρb2, hBt2, htb2⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨B0m, B1m, hB0m, hB1m, hmcdp⟩ :=
    RicciDeTurckLowOrder.mcd_pair_h1 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bm, hBm, hmcdb⟩ :=
    RicciDeTurckLowOrder.metric_connection_difference_coefficient_sobolev_two_bound
      (I := I) (M := M) hDim g (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨W0, W1, hW0, hW1, hwxip⟩ :=
    exists_metricLoweredConnectionDifference_covariantJetNormSq_one_sub_bound
      (I := I) (M := M) hDim g (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bs, hBs, hwxib⟩ := wXi_self_tame (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  set Jp : ℝ := covariantJetNormSq (I := I) (M := M) g 2 (ipLowCoeff (I := I) (M := M) g)
    with hJpdef
  have hJp : 0 ≤ Jp := jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  set ρ : ℝ := min (min ρt1 ρb1) (min ρt2 ρb2) with hρdef
  have hρ0 : 0 < ρ :=
    lt_min (lt_min hρt1 hρb1) (lt_min hρt2 hρb2)
  let Wb : ℝ → ℝ := fun R => Cw2 * Bt1 ^ 2 * (Bs R) ^ 2
  let Wm : ℝ → ℝ := fun R =>
    2 * (Cw1 * Ct1 ^ 2 * (Bs R) ^ 2 +
      Cw1 * Bt1 ^ 2 * (2 * (W0 R) ^ 2 + 2 * (W1 R) ^ 2))
  let Ib : ℝ → ℝ := fun R => Cip2 * Jp * fr ^ 2 * Wb R
  let Im : ℝ → ℝ := fun R => Cip1 * Jp * fr ^ 2 * Wm R
  let Vb : ℝ → ℝ := fun R => fr * (Bm R) ^ 2 * 2
  let Vd : ℝ → ℝ := fun R => fr * (2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2)
  let Sin : ℝ → ℝ := fun R => Cin1 * Vb R * Ib R
  let K1 : ℝ → ℝ := fun R => Cout * Ct2 ^ 2 * Sin R
  let K2 : ℝ → ℝ := fun R => Cout * Bt2 ^ 2 *
    (2 * (Cin12 * Vd R * Ib R + Cin1 * Vb R * Im R))
  let B : ℝ → ℝ := fun R => 4 * (2 * (K1 R + K2 R))
  have hWb : ∀ R : ℝ, 0 ≤ R → 0 ≤ Wb R := fun R _ =>
    mul_nonneg (mul_nonneg hCw2 (sq_nonneg Bt1)) (sq_nonneg (Bs R))
  have hWm : ∀ R : ℝ, 0 ≤ R → 0 ≤ Wm R := fun R _ =>
    mul_nonneg (by norm_num)
      (add_nonneg
        (mul_nonneg (mul_nonneg hCw1 (sq_nonneg Ct1)) (sq_nonneg (Bs R)))
        (mul_nonneg (mul_nonneg hCw1 (sq_nonneg Bt1))
          (add_nonneg
            (mul_nonneg (by norm_num) (sq_nonneg (W0 R)))
            (mul_nonneg (by norm_num) (sq_nonneg (W1 R))))))
  have hIb : ∀ R : ℝ, 0 ≤ R → 0 ≤ Ib R := fun R hR =>
    mul_nonneg
      (mul_nonneg (mul_nonneg hCip2 hJp) (sq_nonneg fr))
      (hWb R hR)
  have hIm : ∀ R : ℝ, 0 ≤ R → 0 ≤ Im R := fun R hR =>
    mul_nonneg
      (mul_nonneg (mul_nonneg hCip1 hJp) (sq_nonneg fr))
      (hWm R hR)
  have hVb : ∀ R : ℝ, 0 ≤ R → 0 ≤ Vb R := fun R _ =>
    mul_nonneg (mul_nonneg hfr (sq_nonneg (Bm R))) (by norm_num)
  have hVd : ∀ R : ℝ, 0 ≤ R → 0 ≤ Vd R := fun R _ =>
    mul_nonneg hfr
      (add_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg (B0m R)))
        (mul_nonneg (by norm_num) (sq_nonneg (B1m R))))
  have hSin : ∀ R : ℝ, 0 ≤ R → 0 ≤ Sin R := fun R hR =>
    mul_nonneg (mul_nonneg hCin1 (hVb R hR)) (hIb R hR)
  have hK1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K1 R := fun R hR =>
    mul_nonneg (mul_nonneg hCout (sq_nonneg _)) (hSin R hR)
  have hK2 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K2 R := fun R hR =>
    mul_nonneg (mul_nonneg hCout (sq_nonneg _))
      (mul_nonneg (by norm_num) (add_nonneg
        (mul_nonneg (mul_nonneg hCin12 (hVd R hR)) (hIb R hR))
        (mul_nonneg (mul_nonneg hCin1 (hVb R hR)) (hIm R hR))))
  refine ⟨ρ, B, hρ0, ?_, ?_⟩
  · intro R hR
    simp only [B]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (by norm_num) (add_nonneg (hK1 R hR) (hK2 R hR)))
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hs2 : s ^ 2 ≤ (1 : ℝ) :=
    unit_interval_sq_le_one_lip hs.1 hs.2
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [hcQ, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.2),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.2),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : covariantJetNormSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    rw [hcQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP3 : covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hQ3 : covariantJetNormSq (I := I) (M := M) g 3 Q ≤ A ^ 2 := by
    rw [hcQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 3) g U) hs2).trans hU3
  have hPQ2 : covariantJetNormSq (I := I) (M := M) g 2 (P - Q) ≤ D2 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by rw [hcP, hcQ, smul_sub]
    rw [hPQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g (T - U)) hs2).trans hTU2
  have hball : ∀ ρ' : ℝ, ρ ≤ ρ' →
      (‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ' ∧
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ') := by
    intro ρ' hρ'
    constructor
    · rw [hcP, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hTn.trans hρ'))
    · rw [hcQ, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hUn.trans hρ'))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have hPQ : P - Q = s • (T - U) := by rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  set pl2 : ℝ := (1 + A + A ^ 2) ^ 2 with hpl2
  have hb1 : (1 : ℝ) ≤ 1 + A + A ^ 2 := by
    calc
      (1 : ℝ) ≤ 1 + A := le_add_of_nonneg_right hA
      _ ≤ 1 + A + A ^ 2 := le_add_of_nonneg_right (sq_nonneg A)
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (1 + A + A ^ 2) ^ 2 := pow_le_pow_left₀ zero_le_one hb1 2
  have hpl20 : 0 ≤ pl2 := le_trans zero_le_one hpl21
  have hplA2 : A ^ 2 ≤ pl2 := by
    rw [hpl2]
    exact sq_le_one_add_add_sq_sq hA
  have h1A : (1 + A) ^ 2 ≤ 2 * pl2 := by
    rw [hpl2]
    calc
      (1 + A) ^ 2 ≤ (1 + A + A ^ 2) ^ 2 :=
        pow_le_pow_left₀ (add_nonneg zero_le_one hA)
          (le_add_of_nonneg_right (sq_nonneg A)) 2
      _ = 1 * (1 + A + A ^ 2) ^ 2 := (one_mul _).symm
      _ ≤ 2 * (1 + A + A ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
  set u : ℝ := D2 ^ 2 + N ^ 2 with hu
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hpl2u : 0 ≤ pl2 * u := mul_nonneg hpl20 hu0
  have hD2u : D2 ^ 2 ≤ pl2 * u := by
    have h1 : D2 ^ 2 ≤ u := by
      rw [hu]
      exact le_add_of_nonneg_right (sq_nonneg N)
    calc D2 ^ 2 ≤ u := h1
      _ = 1 * u := (one_mul u).symm
      _ ≤ pl2 * u := mul_le_mul_of_nonneg_right hpl21 hu0
  have hA2D : A ^ 2 * D2 ^ 2 ≤ pl2 * u := by
    have h1 : A ^ 2 * D2 ^ 2 ≤ pl2 * D2 ^ 2 :=
      mul_le_mul_of_nonneg_right hplA2 (sq_nonneg _)
    have h2 : pl2 * D2 ^ 2 ≤ pl2 * u := by
      rw [hu]
      exact mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (sq_nonneg N)) hpl20
    exact h1.trans h2
  have hpairfold : ∀ b0 b1 : ℝ,
      (b0 * D2 + b1 * A * D2) ^ 2 ≤
        (2 * b0 ^ 2 + 2 * b1 ^ 2) * (pl2 * u) := by
    intro b0 b1
    have hstep : (b0 * D2 + b1 * A * D2) ^ 2 ≤
        2 * b0 ^ 2 * D2 ^ 2 + 2 * b1 ^ 2 * (A ^ 2 * D2 ^ 2) := by
      calc
        (b0 * D2 + b1 * A * D2) ^ 2 ≤
            2 * (b0 * D2) ^ 2 + 2 * (b1 * A * D2) ^ 2 :=
          add_sq_le_two_sq _ _
        _ = 2 * b0 ^ 2 * D2 ^ 2 +
            2 * b1 ^ 2 * (A ^ 2 * D2 ^ 2) := by ring
    refine hstep.trans ?_
    have e1 : 2 * b0 ^ 2 * D2 ^ 2 ≤ 2 * b0 ^ 2 * (pl2 * u) :=
      mul_le_mul_of_nonneg_left hD2u (by positivity)
    have e2 : 2 * b1 ^ 2 * (A ^ 2 * D2 ^ 2) ≤ 2 * b1 ^ 2 * (pl2 * u) :=
      mul_le_mul_of_nonneg_left hA2D (by positivity)
    calc
      2 * b0 ^ 2 * D2 ^ 2 + 2 * b1 ^ 2 * (A ^ 2 * D2 ^ 2) ≤
          2 * b0 ^ 2 * (pl2 * u) + 2 * b1 ^ 2 * (pl2 * u) :=
        add_le_add e1 e2
      _ = (2 * b0 ^ 2 + 2 * b1 ^ 2) * (pl2 * u) := by ring
  set cdT : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCoefficient (I := I) g gmT with hcdT
  set cdU : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCoefficient (I := I) g gmU with hcdU
  set Tr1T : SmoothCcTensor g 3 1 :=
    reindexedPureTrace (I := I) (M := M) g gmT 1 (Equiv.refl (Fin 3)) with hTr1T
  set Tr1U : SmoothCcTensor g 3 1 :=
    reindexedPureTrace (I := I) (M := M) g gmU 1 (Equiv.refl (Fin 3)) with hTr1U
  set WT : SmoothCcTensor g 0 1 :=
    deTurckVectorFieldCovector (I := I) (M := M) g gmT g with hWTdef
  set WU : SmoothCcTensor g 0 1 :=
    deTurckVectorFieldCovector (I := I) (M := M) g gmU g with hWUdef
  set IpT : SmoothCcTensor g 2 1 := ipLowCc (I := I) (M := M) g WT with hIpT
  set IpU : SmoothCcTensor g 2 1 := ipLowCc (I := I) (M := M) g WU with hIpU
  set VmT : SmoothCcTensor g 1 4 := lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gmT with hVmT
  set VmU : SmoothCcTensor g 1 4 := lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gmU with hVmU
  set LvT : SmoothCcTensor g 4 2 := reindexedCometricDoubleTrace (I := I) (M := M) g gmT with hLvT
  set LvU : SmoothCcTensor g 4 2 := reindexedCometricDoubleTrace (I := I) (M := M) g gmU with hLvU
  set InT : SmoothCcTensor g 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 1 4 VmT IpT with hInT
  set InU : SmoothCcTensor g 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 1 4 VmU IpU with hInU
  have hρc : ρ ≤ ρt1 ∧ ρ ≤ ρb1 ∧ ρ ≤ ρt2 ∧ ρ ≤ ρb2 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      · rw [hρdef]
        first
        | exact le_trans (min_le_left _ _) (min_le_left _ _)
        | exact le_trans (min_le_left _ _) (min_le_right _ _)
        | exact le_trans (min_le_right _ _) (min_le_left _ _)
        | exact le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨hPt1n, hQt1n⟩ := hball ρt1 hρc.1
  obtain ⟨hPb1n, hQb1n⟩ := hball ρb1 hρc.2.1
  obtain ⟨hPt2n, hQt2n⟩ := hball ρt2 hρc.2.2.1
  obtain ⟨hPb2n, hQb2n⟩ := hball ρb2 hρc.2.2.2
  have htp1' := trace_pair_h2_to_sum_lip (I := I) (M := M) g 1
    P Q gmT gmU hPtie hQtie ρt1 Ct1 D2 N hPt1n hQt1n hPQn hCt1 htp1
  have htb1' := trace_pair_h2_bdd_lip (I := I) (M := M) g 1
    P Q gmT gmU hPtie hQtie ρb1 Bt1 hPb1n hQb1n htb1
  have htp2' := trace_pair_h2_to_sum_lip (I := I) (M := M) g 2
    P Q gmT gmU hPtie hQtie ρt2 Ct2 D2 N hPt2n hQt2n hPQn hCt2 htp2
  have htb2' := trace_pair_h2_bdd_lip (I := I) (M := M) g 2
    P Q gmT gmU hPtie hQtie ρb2 Bt2 hPb2n hQb2n htb2
  have hmbT : covariantJetNormSq (I := I) (M := M) g 2
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmT g) ≤
        (Bm R) ^ 2 * (2 * pl2) := by
    refine (hmcdb gmT P hPsymm hPtie hδ_le hδ0 hδP R A hR hA hP2 hP3).trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left h1A (sq_nonneg _)
  have hmbU : covariantJetNormSq (I := I) (M := M) g 2
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmU g) ≤
        (Bm R) ^ 2 * (2 * pl2) := by
    refine (hmcdb gmU Q hQsymm hQtie hδ_le hδ0 hδQ R A hR hA hQ2 hQ3).trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left h1A (sq_nonneg _)
  have hmpd : covariantJetNormSq (I := I) (M := M) g 1
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmT g -
        metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmU g) ≤
        (2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2) * (pl2 * u) := by
    exact (hmcdp gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδ_le hδ0 hδQ R A D2 hR hA hD2 hQ2 hP3 hPQ2).trans
      (hpairfold (B0m R) (B1m R))
  have hcdT2 : covariantJetNormSq (I := I) (M := M) g 2 cdT ≤ (Bs R) ^ 2 * pl2 := by
    rw [hcdT, ← metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc (I := I) (M := M) g gmT]
    refine (hwxib gmT P hPsymm hPtie hδ_le hδ0 hδP hδZ R A hR hA hP2 hP3).trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hplA2 (sq_nonneg _)
  have hcdT1 : covariantJetNormSq (I := I) (M := M) g 1 cdT ≤ (Bs R) ^ 2 * pl2 :=
    le_trans (jet_mono_lip (I := I) (M := M) g (by norm_num) cdT) hcdT2
  have hcdd1 : covariantJetNormSq (I := I) (M := M) g 1 (cdT - cdU) ≤
      (2 * (W0 R) ^ 2 + 2 * (W1 R) ^ 2) * (pl2 * u) := by
    rw [hcdT, hcdU, ← metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc (I := I) (M := M) g gmT,
      ← metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc (I := I) (M := M) g gmU]
    exact (hwxip gmT gmU g P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδ_le hδ0 hδQ R A D2 hR hA hD2 hQ2 hP3 hPQ2).trans
      (hpairfold (W0 R) (W1 R))
  have hTr1U2 : covariantJetNormSq (I := I) (M := M) g 2 Tr1U ≤ Bt1 ^ 2 := by
    rw [hTr1U, covariantJetNormSq_reindexedPureTrace]
    exact htb1'.2
  have hTr1T2 : covariantJetNormSq (I := I) (M := M) g 2 Tr1T ≤ Bt1 ^ 2 := by
    rw [hTr1T, covariantJetNormSq_reindexedPureTrace]
    exact htb1'.1
  have hTr1d2 : covariantJetNormSq (I := I) (M := M) g 2 (Tr1T - Tr1U) ≤ Ct1 ^ 2 * u := by
    rw [hTr1T, hTr1U, reindexedPureTrace_sub, covariantJetNormSq_reindexCoefficientInputSlots]
    exact htp1'
  have hWTform : WT = ccOperatorFieldComp (I := I) (M := M) g 0 3 1 Tr1T cdT := by
    rw [hWTdef, hTr1T, hcdT, deTurckVectorFieldCovector_eq_reindexedPureTrace_ccOperatorFieldComp]
  have hWUform : WU = ccOperatorFieldComp (I := I) (M := M) g 0 3 1 Tr1U cdU := by
    rw [hWUdef, hTr1U, hcdU, deTurckVectorFieldCovector_eq_reindexedPureTrace_ccOperatorFieldComp]
  have hWT2 : covariantJetNormSq (I := I) (M := M) g 2 WT ≤ Wb R * pl2 := by
    rw [hWTform]
    refine (happW2 Tr1T cdT).trans ?_
    calc
      Cw2 * covariantJetNormSq (I := I) (M := M) g 2 Tr1T *
          covariantJetNormSq (I := I) (M := M) g 2 cdT ≤
          Cw2 * Bt1 ^ 2 * ((Bs R) ^ 2 * pl2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hTr1T2 hCw2) hcdT2
          (jet_nonneg_lip (I := I) (M := M) (m := 2) g cdT)
          (mul_nonneg hCw2 (sq_nonneg _))
      _ = Wb R * pl2 := by simp only [Wb]; ac_rfl
  have hWd1 : covariantJetNormSq (I := I) (M := M) g 1 (WT - WU) ≤ Wm R * (pl2 * u) := by
    rw [hWTform, hWUform]
    refine (app_pair_h21_lip (I := I) (M := M) g Cw1
      (Ct1 ^ 2 * u) ((Bs R) ^ 2 * pl2) (Bt1 ^ 2)
      ((2 * (W0 R) ^ 2 + 2 * (W1 R) ^ 2) * (pl2 * u))
      hCw1 (mul_nonneg (sq_nonneg _) hu0) (sq_nonneg _)
      Tr1T Tr1U cdT cdU happW1 hTr1d2 hcdT1 hTr1U2 hcdd1).trans ?_
    simp only [Wm]
    exact le_of_eq (vb_w_pair_factor_lip Cw1 Ct1 Bt1 (Bs R)
      (W0 R) (W1 R) pl2 u)
  obtain ⟨hIpT2', hIpT1', hIpd1'⟩ :=
    ipLowCc_bounds_lip (I := I) (M := M) g Cip1 Cip2 Jp
      (Wb R) (Wm R) pl2 u hCip1 hCip2 hJp WT WU
      happIp1 happIp2 hJpdef.symm hWT2 hWd1
  have hIpT2 : covariantJetNormSq (I := I) (M := M) g 2 IpT ≤ Ib R * pl2 := by
    rw [hIpT]
    simpa only [Ib, hfrdef] using hIpT2'
  have hIpT1 : covariantJetNormSq (I := I) (M := M) g 1 IpT ≤ Ib R * pl2 := by
    rw [hIpT]
    simpa only [Ib, hfrdef] using hIpT1'
  have hIpd1 : covariantJetNormSq (I := I) (M := M) g 1 (IpT - IpU) ≤ Im R * (pl2 * u) := by
    rw [hIpT, hIpU]
    simpa only [Im, hfrdef] using hIpd1'
  obtain ⟨hVmT2', hVmU2', hVmd1'⟩ :=
    vbmcd_bounds_lip (I := I) (M := M) g gmT gmU
      (Bm R) (B0m R) (B1m R) pl2 u hmbT hmbU hmpd
  have hVmT2 : covariantJetNormSq (I := I) (M := M) g 2 VmT ≤ Vb R * pl2 := by
    rw [hVmT]
    simpa only [Vb, hfrdef] using hVmT2'
  have hVmU2 : covariantJetNormSq (I := I) (M := M) g 2 VmU ≤ Vb R * pl2 := by
    rw [hVmU]
    simpa only [Vb, hfrdef] using hVmU2'
  have hVmd1 : covariantJetNormSq (I := I) (M := M) g 1 (VmT - VmU) ≤ Vd R * (pl2 * u) := by
    rw [hVmT, hVmU]
    simpa only [Vd, hfrdef] using hVmd1'
  obtain ⟨hInT1', hInd1'⟩ :=
    vb_inner_bounds_lip (I := I) (M := M) g Cin12 Cin1
      (Vd R) (Ib R) (Vb R) (Im R) pl2 u hCin12 hCin1
      (hVd R hR) (hVb R hR) hpl20 hpl2u VmT VmU IpT IpU
      happIn12 happIn1 hVmT2 hVmd1 hIpT1 hIpT2 hVmU2 hIpd1
  have hInT1 : covariantJetNormSq (I := I) (M := M) g 1 InT ≤ Sin R * (pl2 * pl2) := by
    rw [hInT]
    simpa only [Sin] using hInT1'
  have hInd1 : covariantJetNormSq (I := I) (M := M) g 1 (InT - InU) ≤
      2 * ((Cin12 * Vd R * Ib R) * ((pl2 * pl2) * u) +
        (Cin1 * Vb R * Im R) * ((pl2 * pl2) * u)) := by
    rw [hInT, hInU]
    exact hInd1'
  have hLvd2 : covariantJetNormSq (I := I) (M := M) g 2 (LvT - LvU) ≤ Ct2 ^ 2 * u := by
    rw [hLvT, hLvU, reindexedCometricDoubleTrace_eq_pureTrace,
      reindexedCometricDoubleTrace_eq_pureTrace]
    exact htp2'
  have hLvU2 : covariantJetNormSq (I := I) (M := M) g 2 LvU ≤ Bt2 ^ 2 := by
    rw [hLvU, reindexedCometricDoubleTrace_eq_pureTrace]
    exact htb2'.2
  have hFormT : lieCorrectionZeroVectorBundle (I := I) (M := M) g gmT =
      (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 4 2 LvT InT := by
    rw [hLvT, hInT, hVmT, hIpT, hWTdef, lieCorrectionZeroVectorBundle_eq_expansion, lieCorrectionZeroVectorBundleExpansion]
  have hFormU : lieCorrectionZeroVectorBundle (I := I) (M := M) g gmU =
      (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 4 2 LvU InU := by
    rw [hLvU, hInU, hVmU, hIpU, hWUdef, lieCorrectionZeroVectorBundle_eq_expansion, lieCorrectionZeroVectorBundleExpansion]
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (lieCorrectionZeroVectorBundle (I := I) (M := M) g gmT - lieCorrectionZeroVectorBundle (I := I) (M := M) g gmU) ≤
        4 * (2 * (Cout * (Ct2 ^ 2 * u) * (Sin R * (pl2 * pl2)) +
          Cout * Bt2 ^ 2 *
            (2 * ((Cin12 * Vd R * Ib R) * ((pl2 * pl2) * u) +
              (Cin1 * Vb R * Im R) * ((pl2 * pl2) * u))))) :=
      vb_outer_bounds_lip (I := I) (M := M) g gmT gmU
        Cout Ct2 Bt2 (Sin R) (Cin12 * Vd R * Ib R) (Cin1 * Vb R * Im R)
        pl2 u hCout hu0
        LvT LvU InT InU happOut hLvd2 hInT1 hLvU2 hInd1 hFormT hFormU
    _ = B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
      simp only [B, K1, K2, hpl2, hu]
      exact vb_outer_factorization_lip Cout Ct2 Bt2 (Sin R)
        (Cin12 * Vd R * Ib R) (Cin1 * Vb R * Im R) (1 + A + A ^ 2) D2 N

private theorem amixHalf_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 N : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (σlast : Equiv.Perm (Fin 4)),
      covariantJetNormSq (I := I) (M := M) g 1
          (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g σlast -
            lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g σlast) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
  obtain ⟨Ca1, hCa1, happ1⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 2 4 2
  obtain ⟨Ca2, hCa2, happ2⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 2 6 4
  obtain ⟨Ca3, hCa3, happ3⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 2 3 6
  obtain ⟨Ca3f, hCa3f, happ3f⟩ :=
    app_h12_mul_lip (I := I) (M := M) hDim g 2 3 6
  obtain ⟨Ca4, hCa4, happ4⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 2 5 3
  obtain ⟨Ca4b, hCa4b, happ4b⟩ :=
    app_h2_mul_lip (I := I) (M := M) hDim g 2 5 3
  obtain ⟨ρt2, Ct2, hρt2, hCt2, htp2⟩ :=
    RicciDeTurckLowOrder.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρt3, Ct3, hρt3, hCt3, htp3⟩ :=
    RicciDeTurckLowOrder.trace3_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρt4, Ct4, hρt4, hCt4, htp4⟩ :=
    RicciDeTurckLowOrder.trace4_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb2, Bt2, hρb2, hBt2, htb2⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρb3, Bt3, hρb3, hBt3, htb3⟩ :=
    RicciDeTurckLowOrder.trace_three_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρb4, Bt4, hρb4, hBt4, htb4⟩ :=
    RicciDeTurckLowOrder.trace_four_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨B0m, B1m, hB0m, hB1m, hmcdp⟩ :=
    RicciDeTurckLowOrder.mcd_pair_h1 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bm, hBm, hmcdb⟩ :=
    RicciDeTurckLowOrder.metric_connection_difference_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  set ρ : ℝ := min (min ρt2 (min ρt3 ρt4)) (min ρb2 (min ρb3 ρb4))
    with hρdef
  have hρ0 : 0 < ρ :=
    lt_min (lt_min hρt2 (lt_min hρt3 hρt4))
      (lt_min hρb2 (lt_min hρb3 hρb4))
  let S5b : ℝ → ℝ := fun R => fr ^ 2 * (Bm R) ^ 2 * 2
  let S4b : ℝ → ℝ := fun R => Ca4b * (Bt3 ^ 2) * S5b R
  let S4b1 : ℝ → ℝ := fun R => Ca4 * (Bt3 ^ 2) * S5b R
  let S3b : ℝ → ℝ := fun R =>
    Ca3 * (fr ^ 3 * (Bm R) ^ 2 * 2) * S4b1 R
  let S2b : ℝ → ℝ := fun R => Ca2 * (Bt4 ^ 2) * S3b R
  let M5 : ℝ → ℝ := fun R =>
    fr ^ 2 * (2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2)
  let K5 : ℝ → ℝ := fun R => Ca4 * (Bt3 ^ 2) * M5 R
  let K4 : ℝ → ℝ := fun R => Ca4 * (Ct3 ^ 2) * S5b R
  let K3 : ℝ → ℝ := fun R =>
    Ca3f * (fr ^ 3 * (2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2)) * S4b R
  let K34 : ℝ → ℝ := fun R =>
    Ca3 * (fr ^ 3 * (Bm R) ^ 2 * 2) * (2 * (K4 R + K5 R))
  let K2 : ℝ → ℝ := fun R => Ca2 * (Ct4 ^ 2) * S3b R
  let K23 : ℝ → ℝ := fun R =>
    Ca2 * (Bt4 ^ 2) * (2 * (K3 R + K34 R))
  let K1 : ℝ → ℝ := fun R => Ca1 * (Ct2 ^ 2) * S2b R
  let K12 : ℝ → ℝ := fun R =>
    Ca1 * (Bt2 ^ 2) * (2 * (K2 R + K23 R))
  let B : ℝ → ℝ := fun R => 2 * (K1 R + K12 R)
  have hS5b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S5b R := fun R hR => by
    have := hBm R hR
    positivity
  have hS4b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S4b R := fun R hR =>
    mul_nonneg (mul_nonneg hCa4b (sq_nonneg _)) (hS5b R hR)
  have hS4b1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ S4b1 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa4 (sq_nonneg _)) (hS5b R hR)
  have hS3b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S3b R := fun R hR =>
    mul_nonneg (mul_nonneg hCa3 (by positivity)) (hS4b1 R hR)
  have hS2b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S2b R := fun R hR =>
    mul_nonneg (mul_nonneg hCa2 (sq_nonneg _)) (hS3b R hR)
  have hM5 : ∀ R : ℝ, 0 ≤ R → 0 ≤ M5 R := fun R hR => by
    positivity
  have hK5 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K5 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa4 (sq_nonneg _)) (hM5 R hR)
  have hK4 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K4 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa4 (sq_nonneg _)) (hS5b R hR)
  have hK3 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K3 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa3f (by positivity)) (hS4b R hR)
  have hK34 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K34 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa3 (by positivity))
      (mul_nonneg (by norm_num) (add_nonneg (hK4 R hR) (hK5 R hR)))
  have hK2 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K2 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa2 (sq_nonneg _)) (hS3b R hR)
  have hK23 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K23 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa2 (sq_nonneg _))
      (mul_nonneg (by norm_num) (add_nonneg (hK3 R hR) (hK34 R hR)))
  have hK1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K1 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa1 (sq_nonneg _)) (hS2b R hR)
  have hK12 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K12 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa1 (sq_nonneg _))
      (mul_nonneg (by norm_num) (add_nonneg (hK2 R hR) (hK23 R hR)))
  refine ⟨ρ, B, hρ0, ?_, ?_⟩
  · intro R hR
    simp only [B]
    exact mul_nonneg (by norm_num) (add_nonneg (hK1 R hR) (hK12 R hR))
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn s hs σlast
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hs2 : s ^ 2 ≤ (1 : ℝ) :=
    unit_interval_sq_le_one_lip hs.1 hs.2
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [hcQ, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem
        (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem
        (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.2),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.2),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : covariantJetNormSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    rw [hcQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP3 : covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hQ3 : covariantJetNormSq (I := I) (M := M) g 3 Q ≤ A ^ 2 := by
    rw [hcQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 3) g U) hs2).trans hU3
  have hPQ2 : covariantJetNormSq (I := I) (M := M) g 2 (P - Q) ≤ D2 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g (T - U)) hs2).trans hTU2
  have hball : ∀ ρ' : ℝ, ρ ≤ ρ' →
      (‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ' ∧
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ') := by
    intro ρ' hρ'
    constructor
    · rw [hcP, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hTn.trans hρ'))
    · rw [hcQ, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hUn.trans hρ'))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤
      N := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  set mcdT : SmoothCcTensor g 0 3 :=
    metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmT g with hmT
  set mcdU : SmoothCcTensor g 0 3 :=
    metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmU g with hmU
  set pl2 : ℝ := (1 + A + A ^ 2) ^ 2 with hpl2
  have hb1 : (1 : ℝ) ≤ 1 + A + A ^ 2 := by
    calc
      (1 : ℝ) ≤ 1 + A := le_add_of_nonneg_right hA
      _ ≤ 1 + A + A ^ 2 := le_add_of_nonneg_right (sq_nonneg A)
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (1 + A + A ^ 2) ^ 2 :=
        pow_le_pow_left₀ zero_le_one hb1 2
  have hpl20 : 0 ≤ pl2 := le_trans zero_le_one hpl21
  have hplA2 : A ^ 2 ≤ pl2 := by
    rw [hpl2]
    exact sq_le_one_add_add_sq_sq hA
  have h1A : (1 + A) ^ 2 ≤ 2 * pl2 := by
    rw [hpl2]
    calc
      (1 + A) ^ 2 ≤ (1 + A + A ^ 2) ^ 2 :=
        pow_le_pow_left₀ (add_nonneg zero_le_one hA)
          (le_add_of_nonneg_right (sq_nonneg A)) 2
      _ = 1 * (1 + A + A ^ 2) ^ 2 := (one_mul _).symm
      _ ≤ 2 * (1 + A + A ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
  set u : ℝ := D2 ^ 2 + N ^ 2 with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    positivity
  have hmbT : covariantJetNormSq (I := I) (M := M) g 2 mcdT ≤
      (Bm R) ^ 2 * (2 * pl2) := by
    rw [hmT]
    refine (hmcdb gmT P hPsymm hPtie hδ_le hδ0 hδP
      R A hR hA hP2 hP3).trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left h1A (sq_nonneg _)
  have hmbU : covariantJetNormSq (I := I) (M := M) g 2 mcdU ≤
      (Bm R) ^ 2 * (2 * pl2) := by
    rw [hmU]
    refine (hmcdb gmU Q hQsymm hQtie hδ_le hδ0 hδQ
      R A hR hA hQ2 hQ3).trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left h1A (sq_nonneg _)
  have hD2u : D2 ^ 2 ≤ pl2 * u := by
    have h1 : D2 ^ 2 ≤ u := by
      rw [hu]
      exact le_add_of_nonneg_right (sq_nonneg N)
    calc
      D2 ^ 2 ≤ u := h1
      _ = 1 * u := (one_mul u).symm
      _ ≤ pl2 * u := mul_le_mul_of_nonneg_right hpl21 hu0
  have hA2D : A ^ 2 * D2 ^ 2 ≤ pl2 * u := by
    calc
      A ^ 2 * D2 ^ 2 ≤ pl2 * D2 ^ 2 :=
        mul_le_mul_of_nonneg_right hplA2 (sq_nonneg _)
      _ ≤ pl2 * u := mul_le_mul_of_nonneg_left
        (by rw [hu]; exact le_add_of_nonneg_right (sq_nonneg N)) hpl20
  have hmpd : covariantJetNormSq (I := I) (M := M) g 1 (mcdT - mcdU) ≤
      (2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2) * (pl2 * u) := by
    have h := hmcdp gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδ_le hδ0 hδQ R A D2 hR hA hD2 hQ2 hP3 hPQ2
    rw [hmT, hmU]
    exact h.trans (affine_pair_sq_le_weight_lip
      (B0m R) (B1m R) A D2 pl2 u hD2u hA2D)
  have hρc : ρ ≤ ρt2 ∧ ρ ≤ ρt3 ∧ ρ ≤ ρt4 ∧ ρ ≤ ρb2 ∧ ρ ≤ ρb3 ∧
      ρ ≤ ρb4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · rw [hρdef]
        first
        | exact le_trans (min_le_left _ _) (min_le_left _ _)
        | exact le_trans (min_le_left _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _))
        | exact le_trans (min_le_left _ _)
            (le_trans (min_le_right _ _) (min_le_right _ _))
        | exact le_trans (min_le_right _ _) (min_le_left _ _)
        | exact le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _))
        | exact le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨hPt2n, hQt2n⟩ := hball ρt2 hρc.1
  obtain ⟨hPt3n, hQt3n⟩ := hball ρt3 hρc.2.1
  obtain ⟨hPt4n, hQt4n⟩ := hball ρt4 hρc.2.2.1
  obtain ⟨hPb2n, hQb2n⟩ := hball ρb2 hρc.2.2.2.1
  obtain ⟨hPb3n, hQb3n⟩ := hball ρb3 hρc.2.2.2.2.1
  obtain ⟨hPb4n, hQb4n⟩ := hball ρb4 hρc.2.2.2.2.2
  have htp2' := trace_pair_h2_to_sum_lip (I := I) (M := M) g 2
    P Q gmT gmU hPtie hQtie ρt2 Ct2 D2 N hPt2n hQt2n hPQn hCt2 htp2
  have htp3' := trace_pair_h2_to_sum_lip (I := I) (M := M) g 3
    P Q gmT gmU hPtie hQtie ρt3 Ct3 D2 N hPt3n hQt3n hPQn hCt3 htp3
  have htp4' := trace_pair_h2_to_sum_lip (I := I) (M := M) g 4
    P Q gmT gmU hPtie hQtie ρt4 Ct4 D2 N hPt4n hQt4n hPQn hCt4 htp4
  have htb2' := trace_pair_h2_bdd_lip (I := I) (M := M) g 2
    P Q gmT gmU hPtie hQtie ρb2 Bt2 hPb2n hQb2n htb2
  have htb3' := trace_pair_h2_bdd_lip (I := I) (M := M) g 3
    P Q gmT gmU hPtie hQtie ρb3 Bt3 hPb3n hQb3n htb3
  have htb4' := trace_pair_h2_bdd_lip (I := I) (M := M) g 4
    P Q gmT gmU hPtie hQtie ρb4 Bt4 hPb4n hQb4n htb4
  set S5T : SmoothCcTensor g 2 5 :=
    slotExtendIter (I := I) (M := M) g 0 3 2 mcdT with hS5Tdef
  set S5U : SmoothCcTensor g 2 5 :=
    slotExtendIter (I := I) (M := M) g 0 3 2 mcdU with hS5Udef
  set S4T : SmoothCcTensor g 2 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 5 3
      (reindexedPureTrace (I := I) (M := M) g gmT 3 LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) S5T
    with hS4Tdef
  set S4U : SmoothCcTensor g 2 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 5 3
      (reindexedPureTrace (I := I) (M := M) g gmU 3 LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) S5U
    with hS4Udef
  set E3T : SmoothCcTensor g 3 6 :=
    slotExtendIter (I := I) (M := M) g 0 3 3 mcdT with hE3Tdef
  set E3U : SmoothCcTensor g 3 6 :=
    slotExtendIter (I := I) (M := M) g 0 3 3 mcdU with hE3Udef
  set S3T : SmoothCcTensor g 2 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 3 6 E3T S4T with hS3Tdef
  set S3U : SmoothCcTensor g 2 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 3 6 E3U S4U with hS3Udef
  set S2T : SmoothCcTensor g 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 6 4
      (reindexedPureTrace (I := I) (M := M) g gmT 4 LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) S3T
    with hS2Tdef
  set S2U : SmoothCcTensor g 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 6 4
      (reindexedPureTrace (I := I) (M := M) g gmU 4 LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) S3U
    with hS2Udef
  have hHalfT : lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gmT g σlast =
      ccOperatorFieldComp (I := I) (M := M) g 2 4 2
        (reindexedPureTrace (I := I) (M := M) g gmT 2 σlast) S2T := rfl
  have hHalfU : lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gmU g σlast =
      ccOperatorFieldComp (I := I) (M := M) g 2 4 2
        (reindexedPureTrace (I := I) (M := M) g gmU 2 σlast) S2U := rfl
  have hmcdT1 : covariantJetNormSq (I := I) (M := M) g 1 mcdT ≤
      (Bm R) ^ 2 * (2 * pl2) :=
    le_trans (jet_mono_lip (I := I) (M := M) g (by norm_num) mcdT) hmbT
  have hS5T1 : covariantJetNormSq (I := I) (M := M) g 1 S5T ≤
      S5b R * pl2 := by
    rw [hS5Tdef]
    have h0 : slotExtendIter (I := I) (M := M) g 0 3 2 mcdT =
        slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 mcdT) := rfl
    rw [h0]
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) ≤
        fr * covariantJetNormSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 0 3 mcdT) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 4 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 1 mcdT) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _) hfr
      _ ≤ fr * (fr * ((Bm R) ^ 2 * (2 * pl2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmcdT1 hfr) hfr
      _ = S5b R * pl2 := by simp only [S5b]; ring
  have hS5T2 : covariantJetNormSq (I := I) (M := M) g 2 S5T ≤
      S5b R * pl2 := by
    rw [hS5Tdef]
    have h0 : slotExtendIter (I := I) (M := M) g 0 3 2 mcdT =
        slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 mcdT) := rfl
    rw [h0]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) ≤
        fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 mcdT) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 4 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 mcdT) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _) hfr
      _ ≤ fr * (fr * ((Bm R) ^ 2 * (2 * pl2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmbT hfr) hfr
      _ = S5b R * pl2 := by simp only [S5b]; ring
  have hE3T2 : covariantJetNormSq (I := I) (M := M) g 2 E3T ≤
      fr ^ 3 * (Bm R) ^ 2 * 2 * pl2 := by
    rw [hE3Tdef]
    have h0 : slotExtendIter (I := I) (M := M) g 0 3 3 mcdT =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) := rfl
    rw [h0]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 2 5
            (slotExtend (I := I) (M := M) g 1 4
              (slotExtend (I := I) (M := M) g 0 3 mcdT))) ≤
        fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 2 5 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 mcdT)) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 4 _) hfr
      _ ≤ fr * (fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 mcdT)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _) hfr) hfr
      _ ≤ fr * (fr * (fr * ((Bm R) ^ 2 * (2 * pl2)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmbT hfr) hfr) hfr
      _ = fr ^ 3 * (Bm R) ^ 2 * 2 * pl2 := by ring
  have hE3U2 : covariantJetNormSq (I := I) (M := M) g 2 E3U ≤
      fr ^ 3 * (Bm R) ^ 2 * 2 * pl2 := by
    rw [hE3Udef]
    have h0 : slotExtendIter (I := I) (M := M) g 0 3 3 mcdU =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdU)) := rfl
    rw [h0]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 2 5
            (slotExtend (I := I) (M := M) g 1 4
              (slotExtend (I := I) (M := M) g 0 3 mcdU))) ≤
        fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdU)) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 2 5 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 mcdU)) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 4 _) hfr
      _ ≤ fr * (fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 mcdU)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _) hfr) hfr
      _ ≤ fr * (fr * (fr * ((Bm R) ^ 2 * (2 * pl2)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmbU hfr) hfr) hfr
      _ = fr ^ 3 * (Bm R) ^ 2 * 2 * pl2 := by ring
  have hpl2u : 0 ≤ pl2 * u := mul_nonneg hpl20 hu0
  have hS4T1 : covariantJetNormSq (I := I) (M := M) g 1 S4T ≤
      S4b1 R * pl2 := by
    rw [hS4Tdef]
    refine (happ4 _ S5T).trans ?_
    have htr := (covariantJetNormSq_reindexedPureTrace (I := I) (M := M) g gmT 3 2
      LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour).le.trans htb3'.1
    calc
      Ca4 * covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g gmT 3 LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) *
        covariantJetNormSq (I := I) (M := M) g 1 S5T ≤
        Ca4 * Bt3 ^ 2 * (S5b R * pl2) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left htr hCa4) hS5T1
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCa4 (sq_nonneg _))
      _ = S4b1 R * pl2 := by simp only [S4b1]; ring
  have hS4T2 : covariantJetNormSq (I := I) (M := M) g 2 S4T ≤
      S4b R * pl2 := by
    rw [hS4Tdef]
    refine (happ4b _ S5T).trans ?_
    have htr := (covariantJetNormSq_reindexedPureTrace (I := I) (M := M) g gmT 3 2
      LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour).le.trans htb3'.1
    calc
      Ca4b * covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g gmT 3 LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) *
        covariantJetNormSq (I := I) (M := M) g 2 S5T ≤
        Ca4b * Bt3 ^ 2 * (S5b R * pl2) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left htr hCa4b) hS5T2
          (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCa4b (sq_nonneg _))
      _ = S4b R * pl2 := by simp only [S4b]; ring
  have hS3T1 : covariantJetNormSq (I := I) (M := M) g 1 S3T ≤
      S3b R * (pl2 * pl2) := by
    rw [hS3Tdef]
    refine (happ3 E3T S4T).trans ?_
    calc
      Ca3 * covariantJetNormSq (I := I) (M := M) g 2 E3T *
        covariantJetNormSq (I := I) (M := M) g 1 S4T ≤
        Ca3 * (fr ^ 3 * (Bm R) ^ 2 * 2 * pl2) * (S4b1 R * pl2) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hE3T2 hCa3) hS4T1
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCa3 (by positivity))
      _ = S3b R * (pl2 * pl2) := by simp only [S3b]; ring
  have hS2T1 : covariantJetNormSq (I := I) (M := M) g 1 S2T ≤
      S2b R * (pl2 * pl2) := by
    rw [hS2Tdef]
    refine (happ2 _ S3T).trans ?_
    have htr := (covariantJetNormSq_reindexedPureTrace (I := I) (M := M) g gmT 4 2
      LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne).le.trans htb4'.1
    calc
      Ca2 * covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g gmT 4 LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) *
        covariantJetNormSq (I := I) (M := M) g 1 S3T ≤
        Ca2 * Bt4 ^ 2 * (S3b R * (pl2 * pl2)) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left htr hCa2) hS3T1
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCa2 (sq_nonneg _))
      _ = S2b R * (pl2 * pl2) := by simp only [S2b]; ring
  have hdel5 : S5T - S5U =
      slotExtend (I := I) (M := M) g 1 4
        (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU)) := by
    rw [hS5Tdef, hS5Udef,
      show slotExtendIter (I := I) (M := M) g 0 3 2 mcdT =
        slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 mcdT) from rfl,
      show slotExtendIter (I := I) (M := M) g 0 3 2 mcdU =
        slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 mcdU) from rfl,
      slotExtend_sub, slotExtend_sub]
  have hd5 : covariantJetNormSq (I := I) (M := M) g 1 (S5T - S5U) ≤
      M5 R * (pl2 * u) := by
    rw [hdel5]
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) ≤
        fr * covariantJetNormSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU)) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 4 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 1 (mcdT - mcdU)) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _) hfr
      _ ≤ fr * (fr * ((2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2) *
          (pl2 * u))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmpd hfr) hfr
      _ = M5 R * (pl2 * u) := by simp only [M5]; ring
  have htrd3 : covariantJetNormSq (I := I) (M := M) g 2
      (reindexedPureTrace (I := I) (M := M) g gmT 3 LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour -
        reindexedPureTrace (I := I) (M := M) g gmU 3 LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) ≤
      Ct3 ^ 2 * u := by
    rw [reindexedPureTrace_sub, covariantJetNormSq_reindexCoefficientInputSlots]
    exact htp3'
  have htrU3 : covariantJetNormSq (I := I) (M := M) g 2
      (reindexedPureTrace (I := I) (M := M) g gmU 3
        LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) ≤ Bt3 ^ 2 :=
    (covariantJetNormSq_reindexedPureTrace (I := I) (M := M) g gmU 3 2
      LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour).le.trans htb3'.2
  have hd4 : covariantJetNormSq (I := I) (M := M) g 1 (S4T - S4U) ≤
      2 * (K4 R * (pl2 * u) + K5 R * (pl2 * u)) := by
    rw [hS4Tdef, hS4Udef]
    refine (app_pair_h21_lip (I := I) (M := M) g Ca4
      (Ct3 ^ 2 * u) (S5b R * pl2) (Bt3 ^ 2) (M5 R * (pl2 * u))
      hCa4
      ((jet_nonneg_lip (I := I) (M := M) (m := 2) g _).trans htrd3)
      ((jet_nonneg_lip (I := I) (M := M) (m := 2) g _).trans htrU3)
      _ _ S5T S5U happ4 htrd3 hS5T1 htrU3 hd5).trans ?_
    simp only [K4, K5]
    exact le_of_eq (amix_pair_factor_one_lip Ca4 Ct3 (S5b R) Bt3
      (M5 R) pl2 u)
  have hdelE3 : E3T - E3U =
      slotExtend (I := I) (M := M) g 2 5
        (slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) := by
    rw [hE3Tdef, hE3Udef,
      show slotExtendIter (I := I) (M := M) g 0 3 3 mcdT =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) from rfl,
      show slotExtendIter (I := I) (M := M) g 0 3 3 mcdU =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdU)) from rfl,
      slotExtend_sub, slotExtend_sub, slotExtend_sub]
  have hdE31 : covariantJetNormSq (I := I) (M := M) g 1 (E3T - E3U) ≤
      fr ^ 3 * (2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2) * (pl2 * u) := by
    rw [hdelE3]
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 2 5
            (slotExtend (I := I) (M := M) g 1 4
              (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU)))) ≤
        fr * covariantJetNormSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 2 5 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 4 _) hfr
      _ ≤ fr * (fr * (fr *
          covariantJetNormSq (I := I) (M := M) g 1 (mcdT - mcdU))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _) hfr) hfr
      _ ≤ fr * (fr * (fr * ((2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2) *
          (pl2 * u)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmpd hfr) hfr) hfr
      _ = fr ^ 3 * (2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2) * (pl2 * u) := by
        ring
  have hd3 : covariantJetNormSq (I := I) (M := M) g 1 (S3T - S3U) ≤
      2 * (K3 R * ((pl2 * pl2) * u) + K34 R * ((pl2 * pl2) * u)) := by
    rw [hS3Tdef, hS3Udef]
    refine (app_pair_h12_h21_lip (I := I) (M := M) g Ca3f Ca3
      (fr ^ 3 * (2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2) * (pl2 * u))
      (S4b R * pl2) (fr ^ 3 * (Bm R) ^ 2 * 2 * pl2)
      (2 * (K4 R * (pl2 * u) + K5 R * (pl2 * u)))
      hCa3f hCa3
      ((jet_nonneg_lip (I := I) (M := M) (m := 1) g _).trans hdE31)
      ((jet_nonneg_lip (I := I) (M := M) (m := 2) g _).trans hE3U2)
      E3T E3U S4T S4U happ3f happ3 hdE31 hS4T2 hE3U2 hd4).trans ?_
    simp only [K3, K34]
    exact le_of_eq (amix_pair_factor_mixed_lip Ca3f
      (fr ^ 3 * (2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2)) (S4b R)
      Ca3 (fr ^ 3 * (Bm R) ^ 2 * 2) (K4 R) (K5 R) pl2 u)
  have htrd4 : covariantJetNormSq (I := I) (M := M) g 2
      (reindexedPureTrace (I := I) (M := M) g gmT 4 LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne -
        reindexedPureTrace (I := I) (M := M) g gmU 4 LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) ≤
      Ct4 ^ 2 * u := by
    rw [reindexedPureTrace_sub, covariantJetNormSq_reindexCoefficientInputSlots]
    exact htp4'
  have htrU4 : covariantJetNormSq (I := I) (M := M) g 2
      (reindexedPureTrace (I := I) (M := M) g gmU 4
        LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) ≤ Bt4 ^ 2 :=
    (covariantJetNormSq_reindexedPureTrace (I := I) (M := M) g gmU 4 2
      LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne).le.trans htb4'.2
  have hd2 : covariantJetNormSq (I := I) (M := M) g 1 (S2T - S2U) ≤
      2 * (K2 R * ((pl2 * pl2) * u) + K23 R * ((pl2 * pl2) * u)) := by
    rw [hS2Tdef, hS2Udef]
    refine (app_pair_h21_lip (I := I) (M := M) g Ca2
      (Ct4 ^ 2 * u) (S3b R * (pl2 * pl2)) (Bt4 ^ 2)
      (2 * (K3 R * ((pl2 * pl2) * u) + K34 R * ((pl2 * pl2) * u)))
      hCa2
      ((jet_nonneg_lip (I := I) (M := M) (m := 2) g _).trans htrd4)
      ((jet_nonneg_lip (I := I) (M := M) (m := 2) g _).trans htrU4)
      _ _ S3T S3U happ2 htrd4 hS3T1 htrU4 hd3).trans ?_
    simp only [K2, K23]
    exact le_of_eq (amix_pair_factor_two_lip Ca2 Ct4 (S3b R) Bt4
      (K3 R) (K34 R) pl2 u)
  have htrd2 : covariantJetNormSq (I := I) (M := M) g 2
      (reindexedPureTrace (I := I) (M := M) g gmT 2 σlast -
        reindexedPureTrace (I := I) (M := M) g gmU 2 σlast) ≤
      Ct2 ^ 2 * u := by
    rw [reindexedPureTrace_sub, covariantJetNormSq_reindexCoefficientInputSlots]
    exact htp2'
  have htrU2 : covariantJetNormSq (I := I) (M := M) g 2
      (reindexedPureTrace (I := I) (M := M) g gmU 2 σlast) ≤ Bt2 ^ 2 :=
    (covariantJetNormSq_reindexedPureTrace (I := I) (M := M) g gmU 2 2 σlast).le.trans htb2'.2
  rw [hu]
  rw [hHalfT, hHalfU]
  refine (app_pair_h21_lip (I := I) (M := M) g Ca1
    (Ct2 ^ 2 * u) (S2b R * (pl2 * pl2)) (Bt2 ^ 2)
    (2 * (K2 R * ((pl2 * pl2) * u) + K23 R * ((pl2 * pl2) * u)))
    hCa1
    ((jet_nonneg_lip (I := I) (M := M) (m := 2) g _).trans htrd2)
    ((jet_nonneg_lip (I := I) (M := M) (m := 2) g _).trans htrU2)
    _ _ S2T S2U happ1 htrd2 hS2T1 htrU2 hd2).trans ?_
  calc
    2 * (Ca1 * (Ct2 ^ 2 * u) * (S2b R * (pl2 * pl2)) +
        Ca1 * Bt2 ^ 2 *
          (2 * (K2 R * ((pl2 * pl2) * u) +
            K23 R * ((pl2 * pl2) * u)))) =
        2 * (K1 R * ((pl2 * pl2) * u) +
          K12 R * ((pl2 * pl2) * u)) := by
      simp only [K1, K12]
      exact amix_pair_factor_two_lip Ca1 Ct2 (S2b R) Bt2
        (K2 R) (K23 R) pl2 u
    _ = B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
      simp only [B, hpl2, hu]
      exact amix_factorization_lip (K1 R) (K12 R) (1 + A + A ^ 2) D2 N
  exact le_rfl

private theorem amix_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 N : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 1
          (lieCorrectionZeroMixedConnection (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g -
            lieCorrectionZeroMixedConnection (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
  obtain ⟨ρ, Bh, hρ, hBh, hhalf⟩ :=
    amixHalf_pair_h1 (I := I) (M := M) hDim g
  refine ⟨ρ, fun R => 16 * Bh R, hρ,
    fun R hR => by
      have := hBh R hR
      linarith, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn s hs
  have hh1 := hhalf T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn hs
    LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne
  have hh2 := hhalf T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn hs
    (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
  have hX0 : 0 ≤ (1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2) := by
    positivity
  rw [lieCorrectionZeroMixedConnection_eq_expansion (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g,
    lieCorrectionZeroMixedConnection_eq_expansion (I := I) (M := M) g
      (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g]
  have hform :
      lieCorrectionZeroMixedConnectionExpansion (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g -
        lieCorrectionZeroMixedConnectionExpansion (I := I) (M := M) g
          (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g =
      (2 : ℝ) •
        ((lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g
              LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne -
          lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
            (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g
              LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) +
        (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g
              (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) -
          lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
            (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g
              (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))) := by
    simp only [lieCorrectionZeroMixedConnectionExpansion]
    module
  rw [hform, jet_smul_lip]
  have hadd := jet_add_lip (I := I) (M := M) g 1
    (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g
          LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne -
      lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
        (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g
          LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
    (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g
          (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) -
      lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g
        (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g
          (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * LieCorrectionZeroFiberOperators.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))
  have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
  calc
    (2 : ℝ) ^ 2 * covariantJetNormSq (I := I) (M := M) g 1 (_ + _) ≤
      (2 : ℝ) ^ 2 * (2 * (covariantJetNormSq (I := I) (M := M) g 1 _ +
        covariantJetNormSq (I := I) (M := M) g 1 _)) :=
      mul_le_mul_of_nonneg_left hadd (by positivity)
    _ ≤ (2 : ℝ) ^ 2 * (2 *
        (Bh R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) +
          Bh R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)))) := by
      have := add_le_add hh1 hh2
      nlinarith only [this]
    _ = 16 * Bh R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
      ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem jet_sub_lip
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S V : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g m (S - V) ≤
      2 * (covariantJetNormSq (I := I) (M := M) g m S +
        covariantJetNormSq (I := I) (M := M) g m V) := by
  have hrw : S - V = S + (-1 : ℝ) • V := by module
  rw [hrw]
  calc
    covariantJetNormSq (I := I) (M := M) g m (S + (-1 : ℝ) • V) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g m S +
          covariantJetNormSq (I := I) (M := M) g m ((-1 : ℝ) • V)) :=
      jet_add_lip (I := I) (M := M) g m S ((-1 : ℝ) • V)
    _ = 2 * (covariantJetNormSq (I := I) (M := M) g m S +
        covariantJetNormSq (I := I) (M := M) g m V) := by
      rw [jet_smul_lip]; ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem grad_l2_sq_lip
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
private theorem grad_h1_le_h2_lip
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g 1
        (covGrad (I := I) (M := M) g r s S) ≤
      covariantJetNormSq (I := I) (M := M) g 2 S := by
  have h0 := grad_l2_sq_lip (I := I) (M := M) g r s 0 S
  have h1 := grad_l2_sq_lip (I := I) (M := M) g r s 1 S
  unfold covariantJetNormSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 ⊢
  rw [h0, h1]
  nlinarith only [sq_nonneg ‖iteratedCovGrad (I := I) g r s 0 S‖,
    sq_nonneg ‖S‖]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem grad_h2_le_h3_lip
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g 2
        (covGrad (I := I) (M := M) g r s S) ≤
      covariantJetNormSq (I := I) (M := M) g 3 S := by
  have h0 := grad_l2_sq_lip (I := I) (M := M) g r s 0 S
  have h1 := grad_l2_sq_lip (I := I) (M := M) g r s 1 S
  have h2 := grad_l2_sq_lip (I := I) (M := M) g r s 2 S
  unfold covariantJetNormSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 h2 ⊢
  rw [h0, h1, h2]
  nlinarith only [sq_nonneg ‖iteratedCovGrad (I := I) g r s 0 S‖,
    sq_nonneg ‖S‖]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
  [SigmaCompactSpace M] in
private theorem ccSymm_sub_lip
    (g : SmoothRiemannianMetric I M) (C D : SmoothCcTensor g 2 2) :
    ccInputSlotSymm (I := I) (M := M) g C -
        ccInputSlotSymm (I := I) (M := M) g D =
      ccInputSlotSymm (I := I) (M := M) g (C - D) := by
  have hC : ccInputSlotSymm (I := I) (M := M) g C =
      (1 / 2 : ℝ) • (C + ccOperatorFieldComp (I := I) (M := M) g 2 2 2 C
        (ccSlotSwapField (I := I) (M := M) g)) := rfl
  have hD : ccInputSlotSymm (I := I) (M := M) g D =
      (1 / 2 : ℝ) • (D + ccOperatorFieldComp (I := I) (M := M) g 2 2 2 D
        (ccSlotSwapField (I := I) (M := M) g)) := rfl
  have hCD : ccInputSlotSymm (I := I) (M := M) g (C - D) =
      (1 / 2 : ℝ) • ((C - D) + ccOperatorFieldComp (I := I) (M := M) g 2 2 2 (C - D)
        (ccSlotSwapField (I := I) (M := M) g)) := rfl
  rw [hC, hD, hCD, operatorFieldComposition_sub_left]
  module

private theorem inputSymm_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ C : SmoothCcTensor g 2 2,
        covariantJetNormSq (I := I) (M := M) g 1
            (ccInputSlotSymm (I := I) (M := M) g C) ≤
          K * covariantJetNormSq (I := I) (M := M) g 1 C := by
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h12_mul_lip (I := I) (M := M) hDim g 2 2 2
  have hKs : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
      (ccSlotSwapField (I := I) (M := M) g) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  refine ⟨2 * (1 + Ca * covariantJetNormSq (I := I) (M := M) g 2
    (ccSlotSwapField (I := I) (M := M) g)), by positivity, ?_⟩
  intro C
  have hC0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 1 C :=
    jet_nonneg_lip (I := I) (M := M) (m := 1) g C
  have happ' :
      covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g 2 2 2 C
            (ccSlotSwapField (I := I) (M := M) g)) ≤
        Ca * covariantJetNormSq (I := I) (M := M) g 2
            (ccSlotSwapField (I := I) (M := M) g) *
          covariantJetNormSq (I := I) (M := M) g 1 C := by
    have h := happ C (ccSlotSwapField (I := I) (M := M) g)
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g 2 2 2 C
            (ccSlotSwapField (I := I) (M := M) g)) ≤
          Ca * covariantJetNormSq (I := I) (M := M) g 1 C *
            covariantJetNormSq (I := I) (M := M) g 2
              (ccSlotSwapField (I := I) (M := M) g) := h
      _ = Ca * covariantJetNormSq (I := I) (M := M) g 2
            (ccSlotSwapField (I := I) (M := M) g) *
          covariantJetNormSq (I := I) (M := M) g 1 C := by ring
  have hsum :
      covariantJetNormSq (I := I) (M := M) g 1
          (C + ccOperatorFieldComp (I := I) (M := M) g 2 2 2 C
            (ccSlotSwapField (I := I) (M := M) g)) ≤
        2 * (1 + Ca * covariantJetNormSq (I := I) (M := M) g 2
            (ccSlotSwapField (I := I) (M := M) g)) *
          covariantJetNormSq (I := I) (M := M) g 1 C := by
    refine (jet_add_lip (I := I) (M := M) g 1 C _).trans ?_
    linarith [happ']
  have hnn : 0 ≤ covariantJetNormSq (I := I) (M := M) g 1
      (C + ccOperatorFieldComp (I := I) (M := M) g 2 2 2 C
        (ccSlotSwapField (I := I) (M := M) g)) :=
    jet_nonneg_lip (I := I) (M := M) (m := 1) g _
  have hform : ccInputSlotSymm (I := I) (M := M) g C =
      (1 / 2 : ℝ) • (C + ccOperatorFieldComp (I := I) (M := M) g 2 2 2 C
        (ccSlotSwapField (I := I) (M := M) g)) := rfl
  rw [hform, jet_smul_lip]
  linarith [hsum, hnn]

private theorem connSec_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gT g) ≤ (B R * A) ^ 2 := by
  obtain ⟨Bs, hBs, hw⟩ := wXi_self_tame (I := I) (M := M) hDim g
  refine ⟨Bs, hBs, ?_⟩
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  rw [connSec_self_h2 (I := I) (M := M) g gT]
  exact hw gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3

private theorem connIns_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContravariantInsertionField (I := I) g gT) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * (B R * A) ^ 2 := by
  obtain ⟨Bs, hBs, hsec⟩ := connSec_bdd_h2 (I := I) (M := M) hDim g
  refine ⟨Bs, hBs, ?_⟩
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hbase := hsec gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  rw [connectionDifferenceContravariantInsertionField_eq_reindex_slotExtend_two
      (I := I) (M := M) g gT, covariantJetNormSq_reindexCoefficientInputSlots]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 2 3
          (slotExtend (I := I) (M := M) g 1 2
            (connectionDifferenceSection (I := I) gT g))) ≤
      (Module.finrank ℝ E : ℝ) * covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 2
          (connectionDifferenceSection (I := I) gT g)) :=
      covariantJetNormSq_slotExtend_le (I := I) (M := M) g 2 3 _
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gT g)) :=
      mul_le_mul_of_nonneg_left
        (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 2 _) hfr
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) * (Bs R * A) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbase hfr) hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 2 * (Bs R * A) ^ 2 := by ring

private theorem connIns_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 1
          (connectionDifferenceContravariantInsertionField (I := I) g gT -
            connectionDifferenceContravariantInsertionField (I := I) g gU) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 *
          (B0 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ :=
    connSec_pair_h1 (I := I) (M := M) hDim g hδ₀0 hδ₀
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU R A D2 hR hA hD2 hU2 hT3 hTU2
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hp := hpair gT gU T U hT hU hTtie hUtie
    hδT_le hδT0 hδT hδU_le hδU0 hδU R A D2 hR hA hD2 hU2 hT3 hTU2
  have hsub :
      connectionDifferenceContravariantInsertionField (I := I) g gT -
          connectionDifferenceContravariantInsertionField (I := I) g gU =
        reindexCoefficientInputSlots (I := I) (M := M) g 3 4
          (slotExtend (I := I) (M := M) g 2 3
            (slotExtend (I := I) (M := M) g 1 2
              (connectionDifferenceSection (I := I) gT g -
                connectionDifferenceSection (I := I) gU g)))
          coreInPerm201 := by
    rw [connectionDifferenceContravariantInsertionField_eq_reindex_slotExtend_two
        (I := I) (M := M) g gT,
      connectionDifferenceContravariantInsertionField_eq_reindex_slotExtend_two
        (I := I) (M := M) g gU,
      slotExtend_sub, slotExtend_sub, reindexCoefficientInputSlots_sub]
    rw [show connectionDifferenceContrInsertionReindexPerm = coreInPerm201 from rfl]
  rw [hsub, covariantJetNormSq_reindexCoefficientInputSlots]
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (slotExtend (I := I) (M := M) g 2 3
          (slotExtend (I := I) (M := M) g 1 2
            (connectionDifferenceSection (I := I) gT g -
              connectionDifferenceSection (I := I) gU g))) ≤
      (Module.finrank ℝ E : ℝ) * covariantJetNormSq (I := I) (M := M) g 1
        (slotExtend (I := I) (M := M) g 1 2
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g)) :=
      covariantJetNormSq_slotExtend_le (I := I) (M := M) g 2 3 _
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) * covariantJetNormSq (I := I) (M := M) g 1
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g)) :=
      mul_le_mul_of_nonneg_left
        (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 2 _) hfr
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          (B0 R * D2 + B1 R * A * D2) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hp hfr) hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
        (B0 R * D2 + B1 R * A * D2) ^ 2 := by ring

private theorem connInn_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContrInsertionInnerField (I := I) g gT) ≤
        (Module.finrank ℝ E : ℝ) * (B R * A) ^ 2 := by
  obtain ⟨Bs, hBs, hsec⟩ := connSec_bdd_h2 (I := I) (M := M) hDim g
  refine ⟨Bs, hBs, ?_⟩
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hbase := hsec gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  rw [connectionDifferenceContrInsertionInnerField_eq_reindex_slotExtend
      (I := I) (M := M) g gT, covariantJetNormSq_reindexCoefficientInputSlots]
  exact (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 2 _).trans
    (mul_le_mul_of_nonneg_left hbase hfr)

private theorem connInn_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 1
          (connectionDifferenceContrInsertionInnerField (I := I) g gT -
            connectionDifferenceContrInsertionInnerField (I := I) g gU) ≤
        (Module.finrank ℝ E : ℝ) * (B0 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ :=
    connSec_pair_h1 (I := I) (M := M) hDim g hδ₀0 hδ₀
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU R A D2 hR hA hD2 hU2 hT3 hTU2
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hp := hpair gT gU T U hT hU hTtie hUtie
    hδT_le hδT0 hδT hδU_le hδU0 hδU R A D2 hR hA hD2 hU2 hT3 hTU2
  have hsub :
      connectionDifferenceContrInsertionInnerField (I := I) g gT -
          connectionDifferenceContrInsertionInnerField (I := I) g gU =
        reindexCoefficientInputSlots (I := I) (M := M) g 2 3
          (slotExtend (I := I) (M := M) g 1 2
            (connectionDifferenceSection (I := I) gT g -
              connectionDifferenceSection (I := I) gU g))
          innerCoreInPerm10 := by
    rw [connectionDifferenceContrInsertionInnerField_eq_reindex_slotExtend
        (I := I) (M := M) g gT,
      connectionDifferenceContrInsertionInnerField_eq_reindex_slotExtend
        (I := I) (M := M) g gU,
      slotExtend_sub, reindexCoefficientInputSlots_sub]
  rw [hsub, covariantJetNormSq_reindexCoefficientInputSlots]
  exact (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 2 _).trans
    (mul_le_mul_of_nonneg_left hp hfr)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem pureCoeff_eq_lip
    (g gm : SmoothRiemannianMetric I M) :
    cometricDoubleTraceCoefficient (I := I) (M := M) g gm =
      pureTrace (I := I) (M := M) g gm 2 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricDoubleTraceCoefficient_toSection, pureTrace_toSection]

omit [NeZero (Module.finrank ℝ E)] in
private theorem fourtrace_jet_le
    (g : SmoothRiemannianMetric I M) (F : SmoothCcTensor g 4 2) :
    covariantJetNormSq (I := I) (M := M) g 2
        (((1 : ℝ) / 2) •
          (reindexCoefficientInputSlots (I := I) (M := M) g 4 2 F fourTraceArgPerm0231
              + reindexCoefficientInputSlots (I := I) (M := M) g 4 2 F fourTraceArgPerm0321
              - F
              - reindexCoefficientInputSlots (I := I) (M := M) g 4 2 F
                  fourTraceArgPerm2301)) ≤
      22 * covariantJetNormSq (I := I) (M := M) g 2 F := by
  have hJ0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 F :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g F
  have hr1 : covariantJetNormSq (I := I) (M := M) g 2
      (reindexCoefficientInputSlots (I := I) (M := M) g 4 2 F fourTraceArgPerm0231) =
      covariantJetNormSq (I := I) (M := M) g 2 F :=
    covariantJetNormSq_reindexCoefficientInputSlots (I := I) (M := M) g F fourTraceArgPerm0231
  have hr2 : covariantJetNormSq (I := I) (M := M) g 2
      (reindexCoefficientInputSlots (I := I) (M := M) g 4 2 F fourTraceArgPerm0321) =
      covariantJetNormSq (I := I) (M := M) g 2 F :=
    covariantJetNormSq_reindexCoefficientInputSlots (I := I) (M := M) g F fourTraceArgPerm0321
  have hr3 : covariantJetNormSq (I := I) (M := M) g 2
      (reindexCoefficientInputSlots (I := I) (M := M) g 4 2 F fourTraceArgPerm2301) =
      covariantJetNormSq (I := I) (M := M) g 2 F :=
    covariantJetNormSq_reindexCoefficientInputSlots (I := I) (M := M) g F fourTraceArgPerm2301
  have e1 := jet_add_lip (I := I) (M := M) g 2
    (reindexCoefficientInputSlots (I := I) (M := M) g 4 2 F fourTraceArgPerm0231)
    (reindexCoefficientInputSlots (I := I) (M := M) g 4 2 F fourTraceArgPerm0321)
  have e2 := jet_sub_lip (I := I) (M := M) g 2
    (reindexCoefficientInputSlots (I := I) (M := M) g 4 2 F fourTraceArgPerm0231 +
      reindexCoefficientInputSlots (I := I) (M := M) g 4 2 F fourTraceArgPerm0321) F
  have e3 := jet_sub_lip (I := I) (M := M) g 2
    (reindexCoefficientInputSlots (I := I) (M := M) g 4 2 F fourTraceArgPerm0231 +
        reindexCoefficientInputSlots (I := I) (M := M) g 4 2 F fourTraceArgPerm0321 - F)
    (reindexCoefficientInputSlots (I := I) (M := M) g 4 2 F fourTraceArgPerm2301)
  rw [jet_smul_lip]
  rw [hr1, hr2] at e1
  rw [hr3] at e3
  linarith [e1, e2, e3, hJ0]

private theorem fourtrace_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (gT : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        covariantJetNormSq (I := I) (M := M) g 2
            (ricciCometricFourTraceCastG0 (I := I) g gT) ≤ 22 * B ^ 2 := by
  obtain ⟨ρ, B, hρ, hB, hbdd⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T gT htie hTn
  have hF : covariantJetNormSq (I := I) (M := M) g 2
      (cometricDoubleTraceCoefficient (I := I) (M := M) g gT) ≤ B ^ 2 := by
    rw [pureCoeff_eq_lip]
    exact hbdd T gT htie hTn
  rw [ricciCometricFourTraceCastG0_eq_reindex_combination (I := I) (M := M) g gT]
  refine (fourtrace_jet_le (I := I) (M := M) g _).trans ?_
  linarith [hF]

private theorem fourtrace_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        covariantJetNormSq (I := I) (M := M) g 2
            (ricciCometricFourTraceCastG0 (I := I) g gT -
              ricciCometricFourTraceCastG0 (I := I) g gU) ≤
          22 * (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hlip⟩ :=
    RicciDeTurckLowOrder.trace2_pair_h2 (I := I) (M := M) hDim g
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hTn hUn
  have hF : covariantJetNormSq (I := I) (M := M) g 2
      (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
        cometricDoubleTraceCoefficient (I := I) (M := M) g gU) ≤
      (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖) ^ 2 := by
    rw [pureCoeff_eq_lip, pureCoeff_eq_lip]
    exact hlip T U gT gU hTtie hUtie hTn hUn
  have hsub :
      ricciCometricFourTraceCastG0 (I := I) g gT -
          ricciCometricFourTraceCastG0 (I := I) g gU =
        ((1 : ℝ) / 2) •
          (reindexCoefficientInputSlots (I := I) (M := M) g 4 2
                (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
                  cometricDoubleTraceCoefficient (I := I) (M := M) g gU)
                fourTraceArgPerm0231
              + reindexCoefficientInputSlots (I := I) (M := M) g 4 2
                  (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
                    cometricDoubleTraceCoefficient (I := I) (M := M) g gU)
                  fourTraceArgPerm0321
              - (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
                  cometricDoubleTraceCoefficient (I := I) (M := M) g gU)
              - reindexCoefficientInputSlots (I := I) (M := M) g 4 2
                  (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
                    cometricDoubleTraceCoefficient (I := I) (M := M) g gU)
                  fourTraceArgPerm2301) := by
    rw [ricciCometricFourTraceCastG0_eq_reindex_combination
        (I := I) (M := M) g gT,
      ricciCometricFourTraceCastG0_eq_reindex_combination
        (I := I) (M := M) g gU,
      reindexCoefficientInputSlots_sub, reindexCoefficientInputSlots_sub, reindexCoefficientInputSlots_sub]
    module
  rw [hsub]
  refine (fourtrace_jet_le (I := I) (M := M) g _).trans ?_
  linarith [hF]

omit [BoundarylessManifold I M] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem decomposition_sub_lipschitz_bound
    (g : SmoothRiemannianMetric I M)
    (G H : SmoothCcTensor g 0 4) (σ : Equiv.Perm (Fin 4)) :
    decompositionKernelContractionMonomialField (I := I) (M := M) g g (G - H) σ =
      decompositionKernelContractionMonomialField (I := I) (M := M) g g G σ -
        decompositionKernelContractionMonomialField (I := I) (M := M) g g H σ := by
  classical
  have hiter : ∀ D : SmoothCcTensor g 0 4,
      slotExtendIter (I := I) (M := M) g 0 4 2 D =
        slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4 D) := fun _ => rfl
  simp only [decompositionKernelContractionMonomialField_eq_movingMetricPairTraceOperator_comp, hiter]
  rw [dom_sub_lip, slotExtend_sub, slotExtend_sub, rsperm_sub_lip,
    operatorFieldComposition_sub_right]

private theorem decomposition_sobolev_one_lipschitz_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (G : SmoothCcTensor g 0 4) (σ : Equiv.Perm (Fin 4)),
        covariantJetNormSq (I := I) (M := M) g 1
            (decompositionKernelContractionMonomialField
              (I := I) (M := M) g g G σ) ≤
          K * covariantJetNormSq (I := I) (M := M) g 1 G := by
  classical
  obtain ⟨C, hC, happ⟩ := app_h21_mul_lip (I := I) (M := M) hDim g 2 6 2
  have hKm : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
      (movingMetricPairTraceOperator (I := I) (M := M) g g) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  refine ⟨C * covariantJetNormSq (I := I) (M := M) g 2
      (movingMetricPairTraceOperator (I := I) (M := M) g g) *
      ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)),
    by positivity, ?_⟩
  intro G σ
  have hiter : ∀ D : SmoothCcTensor g 0 4,
      slotExtendIter (I := I) (M := M) g 0 4 2 D =
        slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4 D) := fun _ => rfl
  simp only [decompositionKernelContractionMonomialField_eq_movingMetricPairTraceOperator_comp, hiter]
  refine (happ _ _).trans ?_
  have hjet : covariantJetNormSq (I := I) (M := M) g 1
      (rsDomDomCongrSection (I := I) (M := M) g 2 6 movingMetricPairTracePermutation
        (slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
              G)))) ≤
      (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) * covariantJetNormSq (I := I) (M := M) g 1 G) := by
    rw [covariantJetNormSq_rsDomDomCongrSection]
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 1 5
            (slotExtend (I := I) (M := M) g 0 4
              (domDomCongrSection (I := I) g
                (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                G))) ≤
        (Module.finrank ℝ E : ℝ) * covariantJetNormSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 0 4
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
              G)) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 5 _
      _ ≤ (Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) * covariantJetNormSq (I := I) (M := M) g 1
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
              G)) :=
        mul_le_mul_of_nonneg_left (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 4 _) hfr
      _ = (Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) * covariantJetNormSq (I := I) (M := M) g 1 G) := by
        rw [dom_h1_lip]
  calc
    C * covariantJetNormSq (I := I) (M := M) g 2
          (movingMetricPairTraceOperator (I := I) (M := M) g g) *
        covariantJetNormSq (I := I) (M := M) g 1
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 movingMetricPairTracePermutation
            (slotExtend (I := I) (M := M) g 1 5
              (slotExtend (I := I) (M := M) g 0 4
                (domDomCongrSection (I := I) g
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                  G)))) ≤
        C * covariantJetNormSq (I := I) (M := M) g 2
            (movingMetricPairTraceOperator (I := I) (M := M) g g) *
          ((Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) *
              covariantJetNormSq (I := I) (M := M) g 1 G)) :=
      mul_le_mul_of_nonneg_left hjet (mul_nonneg hC hKm)
    _ = C * covariantJetNormSq (I := I) (M := M) g 2
          (movingMetricPairTraceOperator (I := I) (M := M) g g) *
        ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)) *
        covariantJetNormSq (I := I) (M := M) g 1 G := by ring

private theorem decomposition_sobolev_two_lipschitz_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (G : SmoothCcTensor g 0 4) (σ : Equiv.Perm (Fin 4)),
        covariantJetNormSq (I := I) (M := M) g 2
            (decompositionKernelContractionMonomialField
              (I := I) (M := M) g g G σ) ≤
          K * covariantJetNormSq (I := I) (M := M) g 2 G := by
  classical
  obtain ⟨C, hC, happ⟩ := app_h2_mul_lip (I := I) (M := M) hDim g 2 6 2
  have hKm : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
      (movingMetricPairTraceOperator (I := I) (M := M) g g) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  refine ⟨C * covariantJetNormSq (I := I) (M := M) g 2
      (movingMetricPairTraceOperator (I := I) (M := M) g g) *
      ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)),
    by positivity, ?_⟩
  intro G σ
  have hiter : ∀ D : SmoothCcTensor g 0 4,
      slotExtendIter (I := I) (M := M) g 0 4 2 D =
        slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4 D) := fun _ => rfl
  simp only [decompositionKernelContractionMonomialField_eq_movingMetricPairTraceOperator_comp, hiter]
  refine (happ _ _).trans ?_
  have hjet : covariantJetNormSq (I := I) (M := M) g 2
      (rsDomDomCongrSection (I := I) (M := M) g 2 6 movingMetricPairTracePermutation
        (slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
              G)))) ≤
      (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) * covariantJetNormSq (I := I) (M := M) g 2 G) := by
    rw [covariantJetNormSq_rsDomDomCongrSection]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 5
            (slotExtend (I := I) (M := M) g 0 4
              (domDomCongrSection (I := I) g
                (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                G))) ≤
        (Module.finrank ℝ E : ℝ) * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 4
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
              G)) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 5 _
      _ ≤ (Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) * covariantJetNormSq (I := I) (M := M) g 2
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
              G)) :=
        mul_le_mul_of_nonneg_left (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 4 _) hfr
      _ = (Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) * covariantJetNormSq (I := I) (M := M) g 2 G) := by
        rw [dom_h2_lip]
  calc
    C * covariantJetNormSq (I := I) (M := M) g 2
          (movingMetricPairTraceOperator (I := I) (M := M) g g) *
        covariantJetNormSq (I := I) (M := M) g 2
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 movingMetricPairTracePermutation
            (slotExtend (I := I) (M := M) g 1 5
              (slotExtend (I := I) (M := M) g 0 4
                (domDomCongrSection (I := I) g
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                  G)))) ≤
        C * covariantJetNormSq (I := I) (M := M) g 2
            (movingMetricPairTraceOperator (I := I) (M := M) g g) *
          ((Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) *
              covariantJetNormSq (I := I) (M := M) g 2 G)) :=
      mul_le_mul_of_nonneg_left hjet (mul_nonneg hC hKm)
    _ = C * covariantJetNormSq (I := I) (M := M) g 2
          (movingMetricPairTraceOperator (I := I) (M := M) g g) *
        ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)) *
        covariantJetNormSq (I := I) (M := M) g 2 G := by ring

private theorem dagLow_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδP : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (A : ℝ), 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gm) ≤
        K * (1 + A ^ 2) := by
  obtain ⟨K, hK, hdag⟩ :=
    exists_ricciConnectionDerivativeCoefficient_covariantJetNormSq_two_radiusFree_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδP A hA hP3
  refine (hdag gm P hP htie hδ_le hδ0 hδP).trans ?_
  exact mul_le_mul_of_nonneg_left (by linarith) hK

private theorem dagLow_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        covariantJetNormSq (I := I) (M := M) g 1
            (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT -
              RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU) ≤
          C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ^ 2 := by
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 3 4 4
  obtain ⟨ρc, Cc, hρc, hCc, hcl⟩ :=
    RicciDeTurckLowOrder.connLow_pair_h2 (I := I) (M := M) hDim g
  have hKp0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  refine ⟨ρc, Ca * covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation) * Cc ^ 2,
    hρc, by positivity, ?_⟩
  intro T U gT gU hTtie hUtie hTn hUn
  have hformT : RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT =
      ccOperatorFieldComp (I := I) (M := M) g 3 4 4
        (permCoeff (I := I) (M := M) g RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation)
        (covGrad (I := I) (M := M) g 3 3
          (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gT)) := rfl
  have hformU : RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU =
      ccOperatorFieldComp (I := I) (M := M) g 3 4 4
        (permCoeff (I := I) (M := M) g RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation)
        (covGrad (I := I) (M := M) g 3 3
          (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gU)) := rfl
  have hsub :
      RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT -
          RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU =
        ccOperatorFieldComp (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation)
          (covGrad (I := I) (M := M) g 3 3
            (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gT -
              RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gU)) := by
    rw [hformT, hformU, covGrad_sub, operatorFieldComposition_sub_right]
  have hg : covariantJetNormSq (I := I) (M := M) g 1
      (covGrad (I := I) (M := M) g 3 3
        (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gT -
          RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gU)) ≤
      (Cc * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖) ^ 2 :=
    (grad_h1_le_h2_lip (I := I) (M := M) g _).trans
      (hcl T U gT gU hTtie hUtie hTn hUn)
  rw [hsub]
  refine (happ _ _).trans ?_
  calc
    Ca * covariantJetNormSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation) *
        covariantJetNormSq (I := I) (M := M) g 1
          (covGrad (I := I) (M := M) g 3 3
            (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gT -
              RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gU)) ≤
        Ca * covariantJetNormSq (I := I) (M := M) g 2
            (permCoeff (I := I) (M := M) g RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation) *
          (Cc * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hg (mul_nonneg hCa hKp0)
    _ = Ca * covariantJetNormSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation) * Cc ^ 2 *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ^ 2 := by ring

private def aaP3201 : Equiv.Perm (Fin 4) :=
  ⟨![3, 2, 0, 1], ![2, 3, 1, 0], by decide, by decide⟩

private def aaP2301 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

private def aaP3102 : Equiv.Perm (Fin 4) :=
  ⟨![3, 1, 0, 2], ![2, 1, 3, 0], by decide, by decide⟩

private def aaP1302 : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

private def aaP1203 : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

private def aaP2103 : Equiv.Perm (Fin 4) :=
  ⟨![2, 1, 0, 3], ![2, 1, 0, 3], by decide, by decide⟩

private def aaP102 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def aaP120 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

private noncomputable def aaInn
    (g gm : SmoothRiemannianMetric I M) (ρ : Equiv.Perm (Fin 3)) :
    SmoothCcTensor g 2 3 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 3 3
    (permCoeff (I := I) (M := M) g ρ)
    (connectionDifferenceContrInsertionInnerField (I := I) g gm)

private noncomputable def aaBlk
    (g gm : SmoothRiemannianMetric I M) (pm : Equiv.Perm (Fin 4))
    (Z : SmoothCcTensor g 2 3) : SmoothCcTensor g 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 4 4
    (permCoeff (I := I) (M := M) g pm)
    (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g gm) Z)

private noncomputable def aaKerBlockSum
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  aaBlk (I := I) (M := M) g gm aaP3201
          (aaInn (I := I) (M := M) g gm aaP102) +
        reindexCoefficientInputSlots (I := I) (M := M) g 2 4
          (aaBlk (I := I) (M := M) g gm aaP2301
            (aaInn (I := I) (M := M) g gm aaP102)) innerCoreInPerm10 +
        aaBlk (I := I) (M := M) g gm aaP3102
          (aaInn (I := I) (M := M) g gm aaP120) +
        reindexCoefficientInputSlots (I := I) (M := M) g 2 4
          (aaBlk (I := I) (M := M) g gm aaP1302
            (connectionDifferenceContrInsertionInnerField (I := I) g gm))
          innerCoreInPerm10 +
        aaBlk (I := I) (M := M) g gm aaP1203
          (connectionDifferenceContrInsertionInnerField (I := I) g gm) +
        reindexCoefficientInputSlots (I := I) (M := M) g 2 4
          (aaBlk (I := I) (M := M) g gm aaP2103
            (aaInn (I := I) (M := M) g gm aaP120)) innerCoreInPerm10

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem aaKer_eq_lip (g gm : SmoothRiemannianMetric I M) :
    ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gm =
      aaKerBlockSum (I := I) (M := M) g gm := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  unfold ricciConnectionDifferenceQuadraticKernel aaKerBlockSum
  rfl

private noncomputable def aaPK (g : SmoothRiemannianMetric I M) : ℝ :=
  covariantJetNormSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g aaP3201) +
    covariantJetNormSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g aaP2301) +
    covariantJetNormSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g aaP3102) +
    covariantJetNormSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g aaP1302) +
    covariantJetNormSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g aaP1203) +
    covariantJetNormSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g aaP2103) +
    covariantJetNormSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g aaP102) +
    covariantJetNormSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g aaP120)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem aaPK_nonneg (g : SmoothRiemannianMetric I M) :
    0 ≤ aaPK (I := I) (M := M) g := by
  unfold aaPK
  have h1 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP3201) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h2 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP2301) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h3 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP3102) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h4 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP1302) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h5 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP1203) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h6 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP2103) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h7 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP102) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h8 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP120) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  linarith

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem aaPK_ge4 (g : SmoothRiemannianMetric I M)
    (pm : Equiv.Perm (Fin 4))
    (hpm : pm = aaP3201 ∨ pm = aaP2301 ∨ pm = aaP3102 ∨ pm = aaP1302 ∨
      pm = aaP1203 ∨ pm = aaP2103) :
    covariantJetNormSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g pm) ≤
      aaPK (I := I) (M := M) g := by
  have h1 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP3201) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h2 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP2301) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h3 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP3102) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h4 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP1302) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h5 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP1203) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h6 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP2103) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h7 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP102) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h8 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP120) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  unfold aaPK
  rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl <;> linarith

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem aaPK_ge3 (g : SmoothRiemannianMetric I M)
    (ρ : Equiv.Perm (Fin 3)) (hρ : ρ = aaP102 ∨ ρ = aaP120) :
    covariantJetNormSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g ρ) ≤
      aaPK (I := I) (M := M) g := by
  have h1 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP3201) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h2 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP2301) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h3 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP3102) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h4 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP1302) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h5 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP1203) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h6 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP2103) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h7 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP102) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h8 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP120) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  unfold aaPK
  rcases hρ with rfl | rfl <;> linarith

private theorem aaBlk_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M) (pm : Equiv.Perm (Fin 4))
        (Z : SmoothCcTensor g 2 3),
        covariantJetNormSq (I := I) (M := M) g 2
            (aaBlk (I := I) (M := M) g gm pm Z) ≤
          C * (covariantJetNormSq (I := I) (M := M) g 2
              (permCoeff (I := I) (M := M) g pm) *
            (covariantJetNormSq (I := I) (M := M) g 2
                (connectionDifferenceContravariantInsertionField (I := I) g gm) *
              covariantJetNormSq (I := I) (M := M) g 2 Z)) := by
  obtain ⟨C244, hC244, h244⟩ := app_h2_mul_lip (I := I) (M := M) hDim g 2 4 4
  obtain ⟨C234, hC234, h234⟩ := app_h2_mul_lip (I := I) (M := M) hDim g 2 3 4
  refine ⟨C244 * C234, mul_nonneg hC244 hC234, ?_⟩
  intro gm pm Z
  have hp0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g pm) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have hform : aaBlk (I := I) (M := M) g gm pm Z =
      ccOperatorFieldComp (I := I) (M := M) g 2 4 4
        (permCoeff (I := I) (M := M) g pm)
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
          (connectionDifferenceContravariantInsertionField (I := I) g gm) Z) := rfl
  rw [hform]
  refine (h244 (permCoeff (I := I) (M := M) g pm) _).trans ?_
  calc
    C244 * covariantJetNormSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g pm) *
        covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
            (connectionDifferenceContravariantInsertionField (I := I) g gm) Z) ≤
        C244 * covariantJetNormSq (I := I) (M := M) g 2
            (permCoeff (I := I) (M := M) g pm) *
          (C234 * covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceContravariantInsertionField (I := I) g gm) *
            covariantJetNormSq (I := I) (M := M) g 2 Z) :=
      mul_le_mul_of_nonneg_left
        (h234 (connectionDifferenceContravariantInsertionField (I := I) g gm) Z)
        (mul_nonneg hC244 hp0)
    _ = C244 * C234 * (covariantJetNormSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g pm) *
        (covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceContravariantInsertionField (I := I) g gm) *
          covariantJetNormSq (I := I) (M := M) g 2 Z)) := by ring

private theorem aaBlk_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M) (pm : Equiv.Perm (Fin 4))
        (ZT ZU : SmoothCcTensor g 2 3),
        covariantJetNormSq (I := I) (M := M) g 1
            (aaBlk (I := I) (M := M) g gT pm ZT -
              aaBlk (I := I) (M := M) g gU pm ZU) ≤
          C * (covariantJetNormSq (I := I) (M := M) g 2
              (permCoeff (I := I) (M := M) g pm) *
            (covariantJetNormSq (I := I) (M := M) g 1
                (connectionDifferenceContravariantInsertionField (I := I) g gT -
                  connectionDifferenceContravariantInsertionField (I := I) g gU) *
                covariantJetNormSq (I := I) (M := M) g 2 ZT +
              covariantJetNormSq (I := I) (M := M) g 2
                  (connectionDifferenceContravariantInsertionField (I := I) g gU) *
                covariantJetNormSq (I := I) (M := M) g 1 (ZT - ZU))) := by
  obtain ⟨Ca, hCa, hout⟩ := app_h21_mul_lip (I := I) (M := M) hDim g 2 4 4
  obtain ⟨Cf, hCf, hleft⟩ := app_h12_mul_lip (I := I) (M := M) hDim g 2 3 4
  obtain ⟨Cb, hCb, hright⟩ := app_h21_mul_lip (I := I) (M := M) hDim g 2 3 4
  refine ⟨2 * Ca * (Cf + Cb), by positivity, ?_⟩
  intro gT gU pm ZT ZU
  have hp0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g pm) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have ha0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 1
        (connectionDifferenceContravariantInsertionField (I := I) g gT -
          connectionDifferenceContravariantInsertionField (I := I) g gU) *
      covariantJetNormSq (I := I) (M := M) g 2 ZT :=
    mul_nonneg (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
  have hb0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceContravariantInsertionField (I := I) g gU) *
      covariantJetNormSq (I := I) (M := M) g 1 (ZT - ZU) :=
    mul_nonneg (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
      (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
  have hformT : aaBlk (I := I) (M := M) g gT pm ZT =
      ccOperatorFieldComp (I := I) (M := M) g 2 4 4
        (permCoeff (I := I) (M := M) g pm)
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
          (connectionDifferenceContravariantInsertionField (I := I) g gT) ZT) := rfl
  have hformU : aaBlk (I := I) (M := M) g gU pm ZU =
      ccOperatorFieldComp (I := I) (M := M) g 2 4 4
        (permCoeff (I := I) (M := M) g pm)
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
          (connectionDifferenceContravariantInsertionField (I := I) g gU) ZU) := rfl
  have hinner : ccOperatorFieldComp (I := I) (M := M) g 2 3 4
        (connectionDifferenceContravariantInsertionField (I := I) g gT -
          connectionDifferenceContravariantInsertionField (I := I) g gU) ZT +
      ccOperatorFieldComp (I := I) (M := M) g 2 3 4
        (connectionDifferenceContravariantInsertionField (I := I) g gU) (ZT - ZU) =
      ccOperatorFieldComp (I := I) (M := M) g 2 3 4
          (connectionDifferenceContravariantInsertionField (I := I) g gT) ZT -
        ccOperatorFieldComp (I := I) (M := M) g 2 3 4
          (connectionDifferenceContravariantInsertionField (I := I) g gU) ZU := by
    rw [operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
    module
  have hsub : aaBlk (I := I) (M := M) g gT pm ZT -
        aaBlk (I := I) (M := M) g gU pm ZU =
      ccOperatorFieldComp (I := I) (M := M) g 2 4 4
        (permCoeff (I := I) (M := M) g pm)
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
            (connectionDifferenceContravariantInsertionField (I := I) g gT -
              connectionDifferenceContravariantInsertionField (I := I) g gU) ZT +
          ccOperatorFieldComp (I := I) (M := M) g 2 3 4
            (connectionDifferenceContravariantInsertionField (I := I) g gU) (ZT - ZU)) := by
    rw [hformT, hformU, hinner, operatorFieldComposition_sub_right]
  rw [hsub]
  refine (hout _ _).trans ?_
  have h1 : covariantJetNormSq (I := I) (M := M) g 1
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
        (connectionDifferenceContravariantInsertionField (I := I) g gT -
          connectionDifferenceContravariantInsertionField (I := I) g gU) ZT) ≤
      Cf * (covariantJetNormSq (I := I) (M := M) g 1
          (connectionDifferenceContravariantInsertionField (I := I) g gT -
            connectionDifferenceContravariantInsertionField (I := I) g gU) *
        covariantJetNormSq (I := I) (M := M) g 2 ZT) := by
    simpa only [mul_assoc] using
      hleft (connectionDifferenceContravariantInsertionField (I := I) g gT -
        connectionDifferenceContravariantInsertionField (I := I) g gU) ZT
  have h2 : covariantJetNormSq (I := I) (M := M) g 1
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
        (connectionDifferenceContravariantInsertionField (I := I) g gU) (ZT - ZU)) ≤
      Cb * (covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContravariantInsertionField (I := I) g gU) *
        covariantJetNormSq (I := I) (M := M) g 1 (ZT - ZU)) := by
    simpa only [mul_assoc] using
      hright (connectionDifferenceContravariantInsertionField (I := I) g gU) (ZT - ZU)
  have hY : covariantJetNormSq (I := I) (M := M) g 1
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
          (connectionDifferenceContravariantInsertionField (I := I) g gT -
            connectionDifferenceContravariantInsertionField (I := I) g gU) ZT +
        ccOperatorFieldComp (I := I) (M := M) g 2 3 4
          (connectionDifferenceContravariantInsertionField (I := I) g gU) (ZT - ZU)) ≤
      2 * (Cf * (covariantJetNormSq (I := I) (M := M) g 1
            (connectionDifferenceContravariantInsertionField (I := I) g gT -
              connectionDifferenceContravariantInsertionField (I := I) g gU) *
          covariantJetNormSq (I := I) (M := M) g 2 ZT) +
        Cb * (covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceContravariantInsertionField (I := I) g gU) *
          covariantJetNormSq (I := I) (M := M) g 1 (ZT - ZU))) := by
    refine (jet_add_lip (I := I) (M := M) g 1 _ _).trans ?_
    exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num)
  have hstep := mul_le_mul_of_nonneg_left hY (mul_nonneg hCa hp0)
  nlinarith only [hstep,
    mul_nonneg (mul_nonneg (mul_nonneg hCa hp0) hCb) ha0,
    mul_nonneg (mul_nonneg (mul_nonneg hCa hp0) hCf) hb0]

private theorem aaKer_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gT) ≤
        B R * (1 + A + A ^ 2) ^ 4 := by
  obtain ⟨Cblk, hCblk, hblk⟩ := aaBlk_h2 (I := I) (M := M) hDim g
  obtain ⟨C233, hC233, h233⟩ := app_h2_mul_lip (I := I) (M := M) hDim g 2 3 3
  obtain ⟨Bs, hBs, hci⟩ := connIns_bdd_h2 (I := I) (M := M) hDim g
  obtain ⟨Bn, hBn, hcn⟩ := connInn_bdd_h2 (I := I) (M := M) hDim g
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hPK : 0 ≤ aaPK (I := I) (M := M) g := aaPK_nonneg (I := I) (M := M) g
  have hone : (0 : ℝ) ≤ 1 + C233 * aaPK (I := I) (M := M) g := by
    have := mul_nonneg hC233 hPK; linarith
  let B : ℝ → ℝ := fun R =>
    94 * Cblk * (aaPK (I := I) (M := M) g *
      (((Module.finrank ℝ E : ℝ) ^ 2 * Bs R ^ 2) *
        ((1 + C233 * aaPK (I := I) (M := M) g) *
          ((Module.finrank ℝ E : ℝ) * Bn R ^ 2))))
  have hB0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := by
    intro R hR
    have e1 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * Bs R ^ 2 := by positivity
    have e2 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) * Bn R ^ 2 := by positivity
    simp only [B]
    exact mul_nonneg (mul_nonneg (by norm_num) hCblk)
      (mul_nonneg hPK (mul_nonneg e1 (mul_nonneg hone e2)))
  refine ⟨B, hB0, ?_⟩
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  set pl2 : ℝ := (1 + A + A ^ 2) ^ 2 with hpl2
  have hbase : (1 : ℝ) ≤ 1 + A + A ^ 2 := by nlinarith only [hA, sq_nonneg A]
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (1 + A + A ^ 2) ^ 2 := pow_le_pow_left₀ zero_le_one hbase 2
  have hpl20 : (0 : ℝ) ≤ pl2 := le_trans zero_le_one hpl21
  have hplA2 : A ^ 2 ≤ pl2 := by
    rw [hpl2]
    nlinarith only [hA, sq_nonneg A, mul_nonneg hA hA,
      mul_nonneg (mul_nonneg hA hA) hA]
  set CI2 : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Bs R ^ 2 * pl2 with hCI2
  set VN : ℝ := (Module.finrank ℝ E : ℝ) * Bn R ^ 2 * pl2 with hVN
  set ZB : ℝ := (1 + C233 * aaPK (I := I) (M := M) g) * VN with hZB
  have hVN0 : 0 ≤ VN := by
    rw [hVN]
    exact mul_nonneg (by positivity) hpl20
  have hCI20 : 0 ≤ CI2 := by
    rw [hCI2]
    exact mul_nonneg (by positivity) hpl20
  have hci2T : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceContravariantInsertionField (I := I) g gT) ≤ CI2 := by
    refine (hci gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3).trans ?_
    rw [hCI2]
    have hb : (Bs R * A) ^ 2 = Bs R ^ 2 * A ^ 2 := by ring
    rw [hb]
    have hnn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * Bs R ^ 2 := by
      positivity
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hplA2 hnn
  have hcnbase : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceContrInsertionInnerField (I := I) g gT) ≤ VN := by
    refine (hcn gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3).trans ?_
    rw [hVN]
    have hb : (Bn R * A) ^ 2 = Bn R ^ 2 * A ^ 2 := by ring
    rw [hb]
    have hnn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) * Bn R ^ 2 := by positivity
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hplA2 hnn
  have hprodPK : 0 ≤ C233 * aaPK (I := I) (M := M) g * VN :=
    mul_nonneg (mul_nonneg hC233 hPK) hVN0
  have hZdir : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceContrInsertionInnerField (I := I) g gT) ≤ ZB := by
    rw [hZB]
    linarith [hcnbase, hprodPK]
  have hZinn : ∀ ρ : Equiv.Perm (Fin 3), (ρ = aaP102 ∨ ρ = aaP120) →
      covariantJetNormSq (I := I) (M := M) g 2
        (aaInn (I := I) (M := M) g gT ρ) ≤ ZB := by
    intro ρ hρ
    have hpm := aaPK_ge3 (I := I) (M := M) g ρ hρ
    have hp0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
        (permCoeff (I := I) (M := M) g ρ) :=
      jet_nonneg_lip (I := I) (M := M) (m := 2) g _
    have hform : aaInn (I := I) (M := M) g gT ρ =
        ccOperatorFieldComp (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ρ)
          (connectionDifferenceContrInsertionInnerField (I := I) g gT) := rfl
    rw [hform]
    refine (h233 (permCoeff (I := I) (M := M) g ρ) _).trans ?_
    have hstep : C233 * covariantJetNormSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g ρ) *
        covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContrInsertionInnerField (I := I) g gT) ≤
        C233 * aaPK (I := I) (M := M) g * VN :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpm hC233) hcnbase
        (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
        (mul_nonneg hC233 hPK)
    rw [hZB]
    linarith [hstep, hVN0]
  set Q : ℝ := Cblk * (aaPK (I := I) (M := M) g * (CI2 * ZB)) with hQ
  have hZB0 : 0 ≤ ZB := by rw [hZB]; exact mul_nonneg hone hVN0
  have hblkQ : ∀ (pm : Equiv.Perm (Fin 4)),
      (pm = aaP3201 ∨ pm = aaP2301 ∨ pm = aaP3102 ∨ pm = aaP1302 ∨
        pm = aaP1203 ∨ pm = aaP2103) →
      ∀ Z : SmoothCcTensor g 2 3,
      covariantJetNormSq (I := I) (M := M) g 2 Z ≤ ZB →
      covariantJetNormSq (I := I) (M := M) g 2
        (aaBlk (I := I) (M := M) g gT pm Z) ≤ Q := by
    intro pm hpmMem Z hZ
    have hpm := aaPK_ge4 (I := I) (M := M) g pm hpmMem
    refine (hblk gT pm Z).trans ?_
    have hinner : covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContravariantInsertionField (I := I) g gT) *
        covariantJetNormSq (I := I) (M := M) g 2 Z ≤ CI2 * ZB :=
      mul_le_mul hci2T hZ (jet_nonneg_lip (I := I) (M := M) (m := 2) g Z)
        hCI20
    have hmid : covariantJetNormSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g pm) *
        (covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceContravariantInsertionField (I := I) g gT) *
          covariantJetNormSq (I := I) (M := M) g 2 Z) ≤
        aaPK (I := I) (M := M) g * (CI2 * ZB) :=
      mul_le_mul hpm hinner
        (mul_nonneg (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
          (jet_nonneg_lip (I := I) (M := M) (m := 2) g Z))
        hPK
    rw [hQ]
    exact mul_le_mul_of_nonneg_left hmid hCblk
  have hx0 := hblkQ aaP3201 (Or.inl rfl) _ (hZinn aaP102 (Or.inl rfl))
  have hx1 := hblkQ aaP2301 (Or.inr (Or.inl rfl)) _
    (hZinn aaP102 (Or.inl rfl))
  have hx2 := hblkQ aaP3102 (Or.inr (Or.inr (Or.inl rfl))) _
    (hZinn aaP120 (Or.inr rfl))
  have hx3 := hblkQ aaP1302 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _ hZdir
  have hx4 := hblkQ aaP1203
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) _ hZdir
  have hx5 := hblkQ aaP2103
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) _
    (hZinn aaP120 (Or.inr rfl))
  have hrx : ∀ X : SmoothCcTensor g 2 4,
      covariantJetNormSq (I := I) (M := M) g 2
          (reindexCoefficientInputSlots (I := I) (M := M) g 2 4 X innerCoreInPerm10) =
        covariantJetNormSq (I := I) (M := M) g 2 X := by
    intro X
    rw [covariantJetNormSq_reindexCoefficientInputSlots]
  rw [aaKer_eq_lip (I := I) (M := M) g gT]
  unfold aaKerBlockSum
  set y0 := aaBlk (I := I) (M := M) g gT aaP3201
    (aaInn (I := I) (M := M) g gT aaP102) with hy0
  set y1 := reindexCoefficientInputSlots (I := I) (M := M) g 2 4
    (aaBlk (I := I) (M := M) g gT aaP2301
      (aaInn (I := I) (M := M) g gT aaP102)) innerCoreInPerm10 with hy1
  set y2 := aaBlk (I := I) (M := M) g gT aaP3102
    (aaInn (I := I) (M := M) g gT aaP120) with hy2
  set y3 := reindexCoefficientInputSlots (I := I) (M := M) g 2 4
    (aaBlk (I := I) (M := M) g gT aaP1302
      (connectionDifferenceContrInsertionInnerField (I := I) g gT)) innerCoreInPerm10
    with hy3
  set y4 := aaBlk (I := I) (M := M) g gT aaP1203
    (connectionDifferenceContrInsertionInnerField (I := I) g gT) with hy4
  set y5 := reindexCoefficientInputSlots (I := I) (M := M) g 2 4
    (aaBlk (I := I) (M := M) g gT aaP2103
      (aaInn (I := I) (M := M) g gT aaP120)) innerCoreInPerm10 with hy5
  have hb1 : covariantJetNormSq (I := I) (M := M) g 2 y1 ≤ Q := by
    rw [hy1, hrx]; exact hx1
  have hb3 : covariantJetNormSq (I := I) (M := M) g 2 y3 ≤ Q := by
    rw [hy3, hrx]; exact hx3
  have hb5 : covariantJetNormSq (I := I) (M := M) g 2 y5 ≤ Q := by
    rw [hy5, hrx]; exact hx5
  have s01 : covariantJetNormSq (I := I) (M := M) g 2 (y0 + y1) ≤ 4 * Q :=
    (jet_add_lip (I := I) (M := M) g 2 _ _).trans (by linarith [hx0, hb1])
  have s02 : covariantJetNormSq (I := I) (M := M) g 2 (y0 + y1 + y2) ≤ 10 * Q :=
    (jet_add_lip (I := I) (M := M) g 2 _ _).trans (by linarith [s01, hx2])
  have s03 : covariantJetNormSq (I := I) (M := M) g 2 (y0 + y1 + y2 + y3) ≤ 22 * Q :=
    (jet_add_lip (I := I) (M := M) g 2 _ _).trans (by linarith [s02, hb3])
  have s04 : covariantJetNormSq (I := I) (M := M) g 2 (y0 + y1 + y2 + y3 + y4) ≤
      46 * Q :=
    (jet_add_lip (I := I) (M := M) g 2 _ _).trans (by linarith [s03, hx4])
  have s05 : covariantJetNormSq (I := I) (M := M) g 2
      (y0 + y1 + y2 + y3 + y4 + y5) ≤ 94 * Q :=
    (jet_add_lip (I := I) (M := M) g 2 _ _).trans (by linarith [s04, hb5])
  refine s05.trans ?_
  simp only [B, hQ, hCI2, hZB, hVN, hpl2]
  apply le_of_eq
  ring

private theorem aaKer_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 1
          (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gT -
            ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gU) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * D2 ^ 2) := by
  obtain ⟨Cblk, hCblk, hblk⟩ := aaBlk_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨C233, hC233, h233⟩ := app_h2_mul_lip (I := I) (M := M) hDim g 2 3 3
  obtain ⟨C233p, hC233p, h233p⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 2 3 3
  obtain ⟨Bs, hBs, hci⟩ := connIns_bdd_h2 (I := I) (M := M) hDim g
  obtain ⟨Bn, hBn, hcn⟩ := connInn_bdd_h2 (I := I) (M := M) hDim g
  obtain ⟨Bi0, Bi1, hBi0, hBi1, hcid⟩ :=
    connIns_pair_h1 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bm0, Bm1, hBm0, hBm1, hcnd⟩ :=
    connInn_pair_h1 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hPK : 0 ≤ aaPK (I := I) (M := M) g := aaPK_nonneg (I := I) (M := M) g
  have hone : (0 : ℝ) ≤ 1 + C233 * aaPK (I := I) (M := M) g :=
    add_nonneg zero_le_one (mul_nonneg hC233 hPK)
  have honep : (0 : ℝ) ≤ 1 + C233p * aaPK (I := I) (M := M) g :=
    add_nonneg zero_le_one (mul_nonneg hC233p hPK)
  let B : ℝ → ℝ := fun R =>
    94 * Cblk * (aaPK (I := I) (M := M) g *
      (((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Bi0 R ^ 2 + 2 * Bi1 R ^ 2)) *
          ((1 + C233 * aaPK (I := I) (M := M) g) *
            ((Module.finrank ℝ E : ℝ) * Bn R ^ 2)) +
        ((Module.finrank ℝ E : ℝ) ^ 2 * Bs R ^ 2) *
          ((1 + C233p * aaPK (I := I) (M := M) g) *
            ((Module.finrank ℝ E : ℝ) *
              (2 * Bm0 R ^ 2 + 2 * Bm1 R ^ 2)))))
  have hB0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := by
    intro R hR
    have e1 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
      (2 * Bi0 R ^ 2 + 2 * Bi1 R ^ 2) := by positivity
    have e2 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) * Bn R ^ 2 := by positivity
    have e3 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * Bs R ^ 2 := by
      positivity
    have e4 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) *
      (2 * Bm0 R ^ 2 + 2 * Bm1 R ^ 2) := by positivity
    simp only [B]
    exact mul_nonneg (mul_nonneg (by norm_num) hCblk)
      (mul_nonneg hPK
        (add_nonneg (mul_nonneg e1 (mul_nonneg hone e2))
          (mul_nonneg e3 (mul_nonneg honep e4))))
  refine ⟨B, hB0, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    R A D2 hR hA hD2 hT2 hU2 hT3 hU3 hTU2
  set pl2 : ℝ := (1 + A + A ^ 2) ^ 2 with hpl2
  have hbase : (1 : ℝ) ≤ 1 + A + A ^ 2 := by
    calc
      (1 : ℝ) ≤ 1 + A := le_add_of_nonneg_right hA
      _ ≤ 1 + A + A ^ 2 := le_add_of_nonneg_right (sq_nonneg A)
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (1 + A + A ^ 2) ^ 2 := pow_le_pow_left₀ zero_le_one hbase 2
  have hpl20 : (0 : ℝ) ≤ pl2 := le_trans zero_le_one hpl21
  have hplA2 : A ^ 2 ≤ pl2 := by
    rw [hpl2]
    exact sq_le_one_add_add_sq_sq hA
  have hpu0 : (0 : ℝ) ≤ pl2 * D2 ^ 2 := mul_nonneg hpl20 (sq_nonneg D2)
  have hD2p : D2 ^ 2 ≤ pl2 * D2 ^ 2 := by
    calc
      D2 ^ 2 = 1 * D2 ^ 2 := (one_mul _).symm
      _ ≤ pl2 * D2 ^ 2 := mul_le_mul_of_nonneg_right hpl21 (sq_nonneg D2)
  have hA2D : A ^ 2 * D2 ^ 2 ≤ pl2 * D2 ^ 2 :=
    mul_le_mul_of_nonneg_right hplA2 (sq_nonneg D2)
  have hpairfold : ∀ b0 b1 : ℝ,
      (b0 * D2 + b1 * A * D2) ^ 2 ≤
        (2 * b0 ^ 2 + 2 * b1 ^ 2) * (pl2 * D2 ^ 2) := by
    intro b0 b1
    exact affine_pair_sq_le_weight_lip b0 b1 A D2 pl2 (D2 ^ 2) hD2p hA2D
  set CI2 : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Bs R ^ 2 * pl2 with hCI2
  set CID : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 *
    ((2 * Bi0 R ^ 2 + 2 * Bi1 R ^ 2) * (pl2 * D2 ^ 2)) with hCID
  set VN : ℝ := (Module.finrank ℝ E : ℝ) * Bn R ^ 2 * pl2 with hVN
  set VM : ℝ := (Module.finrank ℝ E : ℝ) *
    ((2 * Bm0 R ^ 2 + 2 * Bm1 R ^ 2) * (pl2 * D2 ^ 2)) with hVM
  set ZB : ℝ := (1 + C233 * aaPK (I := I) (M := M) g) * VN with hZB
  set ZD : ℝ := (1 + C233p * aaPK (I := I) (M := M) g) * VM with hZD
  have hVN0 : 0 ≤ VN := by
    rw [hVN]; exact mul_nonneg (by positivity) hpl20
  have hVM0 : 0 ≤ VM := by
    rw [hVM]
    exact mul_nonneg hfr (mul_nonneg (by positivity) hpu0)
  have hCI20 : 0 ≤ CI2 := by
    rw [hCI2]; exact mul_nonneg (by positivity) hpl20
  have hCID0 : 0 ≤ CID := by
    rw [hCID]
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) hpu0)
  have hZB0 : 0 ≤ ZB := by rw [hZB]; exact mul_nonneg hone hVN0
  have hZD0 : 0 ≤ ZD := by rw [hZD]; exact mul_nonneg honep hVM0
  have hci2U : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceContravariantInsertionField (I := I) g gU) ≤ CI2 := by
    refine (hci gU U hU hUtie hδ_le hδ0 hδU hδZ R A hR hA hU2 hU3).trans ?_
    rw [hCI2]
    have hb : (Bs R * A) ^ 2 = Bs R ^ 2 * A ^ 2 := by ring
    rw [hb]
    have hnn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * Bs R ^ 2 := by
      positivity
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hplA2 hnn
  have hcidT : covariantJetNormSq (I := I) (M := M) g 1
      (connectionDifferenceContravariantInsertionField (I := I) g gT -
        connectionDifferenceContravariantInsertionField (I := I) g gU) ≤ CID := by
    refine (hcid gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδ_le hδ0 hδU
      R A D2 hR hA hD2 hU2 hT3 hTU2).trans ?_
    rw [hCID]
    have hnn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left (hpairfold (Bi0 R) (Bi1 R)) hnn
  have hcnbase : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceContrInsertionInnerField (I := I) g gT) ≤ VN := by
    refine (hcn gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3).trans ?_
    rw [hVN]
    have hb : (Bn R * A) ^ 2 = Bn R ^ 2 * A ^ 2 := by ring
    rw [hb]
    have hnn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) * Bn R ^ 2 := by positivity
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hplA2 hnn
  have hcndT : covariantJetNormSq (I := I) (M := M) g 1
      (connectionDifferenceContrInsertionInnerField (I := I) g gT -
        connectionDifferenceContrInsertionInnerField (I := I) g gU) ≤ VM := by
    refine (hcnd gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδ_le hδ0 hδU
      R A D2 hR hA hD2 hU2 hT3 hTU2).trans ?_
    rw [hVM]
    exact mul_le_mul_of_nonneg_left (hpairfold (Bm0 R) (Bm1 R)) hfr
  have hZdirB : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceContrInsertionInnerField (I := I) g gT) ≤ ZB := by
    rw [hZB]
    refine hcnbase.trans ?_
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right
        (show (1 : ℝ) ≤ 1 + C233 * aaPK (I := I) (M := M) g from
          le_add_of_nonneg_right (mul_nonneg hC233 hPK)) hVN0
  have hZdirD : covariantJetNormSq (I := I) (M := M) g 1
      (connectionDifferenceContrInsertionInnerField (I := I) g gT -
        connectionDifferenceContrInsertionInnerField (I := I) g gU) ≤ ZD := by
    rw [hZD]
    refine hcndT.trans ?_
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right
        (show (1 : ℝ) ≤ 1 + C233p * aaPK (I := I) (M := M) g from
          le_add_of_nonneg_right (mul_nonneg hC233p hPK)) hVM0
  have hZinnB : ∀ ρ : Equiv.Perm (Fin 3), (ρ = aaP102 ∨ ρ = aaP120) →
      covariantJetNormSq (I := I) (M := M) g 2
        (aaInn (I := I) (M := M) g gT ρ) ≤ ZB := by
    intro ρ hρ
    have hpm := aaPK_ge3 (I := I) (M := M) g ρ hρ
    have hform : aaInn (I := I) (M := M) g gT ρ =
        ccOperatorFieldComp (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ρ)
          (connectionDifferenceContrInsertionInnerField (I := I) g gT) := rfl
    rw [hform]
    refine (h233 (permCoeff (I := I) (M := M) g ρ) _).trans ?_
    have hstep : C233 * covariantJetNormSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g ρ) *
        covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContrInsertionInnerField (I := I) g gT) ≤
        C233 * aaPK (I := I) (M := M) g * VN :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpm hC233) hcnbase
        (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
        (mul_nonneg hC233 hPK)
    rw [hZB]
    exact hstep.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hVN0)
  have hZinnD : ∀ ρ : Equiv.Perm (Fin 3), (ρ = aaP102 ∨ ρ = aaP120) →
      covariantJetNormSq (I := I) (M := M) g 1
        (aaInn (I := I) (M := M) g gT ρ -
          aaInn (I := I) (M := M) g gU ρ) ≤ ZD := by
    intro ρ hρ
    have hpm := aaPK_ge3 (I := I) (M := M) g ρ hρ
    have hsub : aaInn (I := I) (M := M) g gT ρ -
          aaInn (I := I) (M := M) g gU ρ =
        ccOperatorFieldComp (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ρ)
          (connectionDifferenceContrInsertionInnerField (I := I) g gT -
            connectionDifferenceContrInsertionInnerField (I := I) g gU) := by
      have hfT : aaInn (I := I) (M := M) g gT ρ =
          ccOperatorFieldComp (I := I) (M := M) g 2 3 3
            (permCoeff (I := I) (M := M) g ρ)
            (connectionDifferenceContrInsertionInnerField (I := I) g gT) := rfl
      have hfU : aaInn (I := I) (M := M) g gU ρ =
          ccOperatorFieldComp (I := I) (M := M) g 2 3 3
            (permCoeff (I := I) (M := M) g ρ)
            (connectionDifferenceContrInsertionInnerField (I := I) g gU) := rfl
      rw [hfT, hfU, operatorFieldComposition_sub_right]
    rw [hsub]
    refine (h233p (permCoeff (I := I) (M := M) g ρ) _).trans ?_
    have hstep : C233p * covariantJetNormSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g ρ) *
        covariantJetNormSq (I := I) (M := M) g 1
          (connectionDifferenceContrInsertionInnerField (I := I) g gT -
            connectionDifferenceContrInsertionInnerField (I := I) g gU) ≤
        C233p * aaPK (I := I) (M := M) g * VM :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpm hC233p) hcndT
        (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
        (mul_nonneg hC233p hPK)
    rw [hZD]
    exact hstep.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hVM0)
  set Q : ℝ := Cblk * (aaPK (I := I) (M := M) g * (CID * ZB + CI2 * ZD))
    with hQ
  have hblkQ : ∀ (pm : Equiv.Perm (Fin 4)),
      (pm = aaP3201 ∨ pm = aaP2301 ∨ pm = aaP3102 ∨ pm = aaP1302 ∨
        pm = aaP1203 ∨ pm = aaP2103) →
      ∀ ZT ZU : SmoothCcTensor g 2 3,
      covariantJetNormSq (I := I) (M := M) g 2 ZT ≤ ZB →
      covariantJetNormSq (I := I) (M := M) g 1 (ZT - ZU) ≤ ZD →
      covariantJetNormSq (I := I) (M := M) g 1
        (aaBlk (I := I) (M := M) g gT pm ZT -
          aaBlk (I := I) (M := M) g gU pm ZU) ≤ Q := by
    intro pm hpmMem ZT ZU hzb hzd
    have hpm := aaPK_ge4 (I := I) (M := M) g pm hpmMem
    refine (hblk gT gU pm ZT ZU).trans ?_
    have h1 : covariantJetNormSq (I := I) (M := M) g 1
          (connectionDifferenceContravariantInsertionField (I := I) g gT -
            connectionDifferenceContravariantInsertionField (I := I) g gU) *
        covariantJetNormSq (I := I) (M := M) g 2 ZT ≤ CID * ZB :=
      mul_le_mul hcidT hzb (jet_nonneg_lip (I := I) (M := M) (m := 2) g ZT)
        hCID0
    have h2 : covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContravariantInsertionField (I := I) g gU) *
        covariantJetNormSq (I := I) (M := M) g 1 (ZT - ZU) ≤ CI2 * ZD :=
      mul_le_mul hci2U hzd (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
        hCI20
    have hsum0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 1
          (connectionDifferenceContravariantInsertionField (I := I) g gT -
            connectionDifferenceContravariantInsertionField (I := I) g gU) *
          covariantJetNormSq (I := I) (M := M) g 2 ZT +
        covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceContravariantInsertionField (I := I) g gU) *
          covariantJetNormSq (I := I) (M := M) g 1 (ZT - ZU) :=
      add_nonneg
        (mul_nonneg (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (jet_nonneg_lip (I := I) (M := M) (m := 2) g ZT))
        (mul_nonneg (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _))
    have hmid : covariantJetNormSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g pm) *
        (covariantJetNormSq (I := I) (M := M) g 1
              (connectionDifferenceContravariantInsertionField (I := I) g gT -
                connectionDifferenceContravariantInsertionField (I := I) g gU) *
            covariantJetNormSq (I := I) (M := M) g 2 ZT +
          covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceContravariantInsertionField (I := I) g gU) *
            covariantJetNormSq (I := I) (M := M) g 1 (ZT - ZU)) ≤
        aaPK (I := I) (M := M) g * (CID * ZB + CI2 * ZD) :=
      mul_le_mul hpm (add_le_add h1 h2) hsum0 hPK
    rw [hQ]
    exact mul_le_mul_of_nonneg_left hmid hCblk
  have hx0 := hblkQ aaP3201 (Or.inl rfl) _ _
    (hZinnB aaP102 (Or.inl rfl)) (hZinnD aaP102 (Or.inl rfl))
  have hx1 := hblkQ aaP2301 (Or.inr (Or.inl rfl)) _ _
    (hZinnB aaP102 (Or.inl rfl)) (hZinnD aaP102 (Or.inl rfl))
  have hx2 := hblkQ aaP3102 (Or.inr (Or.inr (Or.inl rfl))) _ _
    (hZinnB aaP120 (Or.inr rfl)) (hZinnD aaP120 (Or.inr rfl))
  have hx3 := hblkQ aaP1302 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _ _
    hZdirB hZdirD
  have hx4 := hblkQ aaP1203
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) _ _ hZdirB hZdirD
  have hx5 := hblkQ aaP2103
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) _ _
    (hZinnB aaP120 (Or.inr rfl)) (hZinnD aaP120 (Or.inr rfl))
  have hrx : ∀ X Y : SmoothCcTensor g 2 4,
      covariantJetNormSq (I := I) (M := M) g 1
          (reindexCoefficientInputSlots (I := I) (M := M) g 2 4 X innerCoreInPerm10 -
            reindexCoefficientInputSlots (I := I) (M := M) g 2 4 Y innerCoreInPerm10) =
        covariantJetNormSq (I := I) (M := M) g 1 (X - Y) := by
    intro X Y
    rw [← reindexCoefficientInputSlots_sub, covariantJetNormSq_reindexCoefficientInputSlots]
  rw [aaKer_eq_lip (I := I) (M := M) g gT,
    aaKer_eq_lip (I := I) (M := M) g gU]
  unfold aaKerBlockSum
  set y0 := aaBlk (I := I) (M := M) g gT aaP3201
    (aaInn (I := I) (M := M) g gT aaP102) with hy0
  set y1 := reindexCoefficientInputSlots (I := I) (M := M) g 2 4
    (aaBlk (I := I) (M := M) g gT aaP2301
      (aaInn (I := I) (M := M) g gT aaP102)) innerCoreInPerm10 with hy1
  set y2 := aaBlk (I := I) (M := M) g gT aaP3102
    (aaInn (I := I) (M := M) g gT aaP120) with hy2
  set y3 := reindexCoefficientInputSlots (I := I) (M := M) g 2 4
    (aaBlk (I := I) (M := M) g gT aaP1302
      (connectionDifferenceContrInsertionInnerField (I := I) g gT)) innerCoreInPerm10
    with hy3
  set y4 := aaBlk (I := I) (M := M) g gT aaP1203
    (connectionDifferenceContrInsertionInnerField (I := I) g gT) with hy4
  set y5 := reindexCoefficientInputSlots (I := I) (M := M) g 2 4
    (aaBlk (I := I) (M := M) g gT aaP2103
      (aaInn (I := I) (M := M) g gT aaP120)) innerCoreInPerm10 with hy5
  set z0 := aaBlk (I := I) (M := M) g gU aaP3201
    (aaInn (I := I) (M := M) g gU aaP102) with hz0
  set z1 := reindexCoefficientInputSlots (I := I) (M := M) g 2 4
    (aaBlk (I := I) (M := M) g gU aaP2301
      (aaInn (I := I) (M := M) g gU aaP102)) innerCoreInPerm10 with hz1
  set z2 := aaBlk (I := I) (M := M) g gU aaP3102
    (aaInn (I := I) (M := M) g gU aaP120) with hz2
  set z3 := reindexCoefficientInputSlots (I := I) (M := M) g 2 4
    (aaBlk (I := I) (M := M) g gU aaP1302
      (connectionDifferenceContrInsertionInnerField (I := I) g gU)) innerCoreInPerm10
    with hz3
  set z4 := aaBlk (I := I) (M := M) g gU aaP1203
    (connectionDifferenceContrInsertionInnerField (I := I) g gU) with hz4
  set z5 := reindexCoefficientInputSlots (I := I) (M := M) g 2 4
    (aaBlk (I := I) (M := M) g gU aaP2103
      (aaInn (I := I) (M := M) g gU aaP120)) innerCoreInPerm10 with hz5
  have hb1 : covariantJetNormSq (I := I) (M := M) g 1 (y1 - z1) ≤ Q := by
    rw [hy1, hz1, hrx]; exact hx1
  have hb3 : covariantJetNormSq (I := I) (M := M) g 1 (y3 - z3) ≤ Q := by
    rw [hy3, hz3, hrx]; exact hx3
  have hb5 : covariantJetNormSq (I := I) (M := M) g 1 (y5 - z5) ≤ Q := by
    rw [hy5, hz5, hrx]; exact hx5
  have hsplit : y0 + y1 + y2 + y3 + y4 + y5 -
      (z0 + z1 + z2 + z3 + z4 + z5) =
      (y0 - z0) + (y1 - z1) + (y2 - z2) + (y3 - z3) + (y4 - z4) +
        (y5 - z5) := by abel
  rw [hsplit]
  have s01 : covariantJetNormSq (I := I) (M := M) g 1 ((y0 - z0) + (y1 - z1)) ≤
      4 * Q := by
    convert jet_add_bound_step_lip (I := I) (M := M) g 1
      (y0 - z0) (y1 - z1) 1 Q (by simpa using hx0) hb1 using 1
    all_goals norm_num
  have s02 : covariantJetNormSq (I := I) (M := M) g 1
      ((y0 - z0) + (y1 - z1) + (y2 - z2)) ≤ 10 * Q :=
    by
      convert jet_add_bound_step_lip (I := I) (M := M) g 1
        ((y0 - z0) + (y1 - z1)) (y2 - z2) 4 Q s01 hx2 using 1
      all_goals norm_num
  have s03 : covariantJetNormSq (I := I) (M := M) g 1
      ((y0 - z0) + (y1 - z1) + (y2 - z2) + (y3 - z3)) ≤ 22 * Q :=
    by
      convert jet_add_bound_step_lip (I := I) (M := M) g 1
        ((y0 - z0) + (y1 - z1) + (y2 - z2)) (y3 - z3) 10 Q s02 hb3 using 1
      all_goals norm_num
  have s04 : covariantJetNormSq (I := I) (M := M) g 1
      ((y0 - z0) + (y1 - z1) + (y2 - z2) + (y3 - z3) + (y4 - z4)) ≤
      46 * Q := by
    convert jet_add_bound_step_lip (I := I) (M := M) g 1
      ((y0 - z0) + (y1 - z1) + (y2 - z2) + (y3 - z3)) (y4 - z4) 22 Q s03 hx4
      using 1
    all_goals norm_num
  have s05 : covariantJetNormSq (I := I) (M := M) g 1
      ((y0 - z0) + (y1 - z1) + (y2 - z2) + (y3 - z3) + (y4 - z4) +
        (y5 - z5)) ≤ 94 * Q := by
    convert jet_add_bound_step_lip (I := I) (M := M) g 1
      ((y0 - z0) + (y1 - z1) + (y2 - z2) + (y3 - z3) + (y4 - z4))
      (y5 - z5) 46 Q s04 hb5 using 1
    all_goals norm_num
  refine s05.trans ?_
  simp only [B, hQ, hCI2, hCID, hZB, hZD, hVN, hVM, hpl2]
  apply le_of_eq
  ring

private theorem ricciConnectionDifferenceQuadratic_pairing_firstOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 N : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 1
          (ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gT -
            ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gU) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
  obtain ⟨Ca, hCa, happ⟩ := app_h21_mul_lip (I := I) (M := M) hDim g 2 4 2
  obtain ⟨ρp, Cft, hρp, hCft, hftp⟩ :=
    fourtrace_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Bft, hρb, hBft, hftb⟩ :=
    fourtrace_bdd_h2 (I := I) (M := M) hDim g
  obtain ⟨Bk, hBk, hkerb⟩ := aaKer_bdd_h2 (I := I) (M := M) hDim g
  obtain ⟨Bd, hBd, hkerd⟩ := aaKer_pair_h1 (I := I) (M := M) hDim g
  let K1 : ℝ → ℝ := fun R => Ca * (22 * Cft ^ 2) * Bk R
  let K2 : ℝ → ℝ := fun R => Ca * (22 * Bft ^ 2) * Bd R
  let B : ℝ → ℝ := fun R => 2 * (K1 R + K2 R)
  have hK10 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K1 R := by
    intro R hR
    have := hBk R hR
    simp only [K1]
    positivity
  have hK20 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K2 R := by
    intro R hR
    have := hBd R hR
    simp only [K2]
    positivity
  refine ⟨min ρp ρb, B, lt_min hρp hρb, ?_, ?_⟩
  · intro R hR
    have e1 := hK10 R hR
    have e2 := hK20 R hR
    simp only [B]
    linarith
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn
  have hρp' : min ρp ρb ≤ ρp := min_le_left _ _
  have hρb' : min ρp ρb ≤ ρb := min_le_right _ _
  set W : ℝ := (1 + A + A ^ 2) ^ 4 with hW
  set u : ℝ := D2 ^ 2 + N ^ 2 with hu
  have hu0 : (0 : ℝ) ≤ u := by rw [hu]; positivity
  have hW0 : (0 : ℝ) ≤ W := by rw [hW]; positivity
  have hNu : N ^ 2 ≤ u := by rw [hu]; nlinarith only [sq_nonneg D2]
  have hDu : D2 ^ 2 ≤ u := by rw [hu]; nlinarith only [sq_nonneg N]
  have hftd : covariantJetNormSq (I := I) (M := M) g 2
      (ricciCometricFourTraceCastG0 (I := I) g gT -
        ricciCometricFourTraceCastG0 (I := I) g gU) ≤
      22 * Cft ^ 2 * u := by
    refine (hftp T U gT gU hTtie hUtie (hTn.trans hρp')
      (hUn.trans hρp')).trans ?_
    have h1 : Cft * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤
        Cft * N := mul_le_mul_of_nonneg_left hTUn hCft
    have h2 : (Cft * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (T - U)‖) ^ 2 ≤ (Cft * N) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hCft (norm_nonneg _)) h1 2
    have h3 : (Cft * N) ^ 2 = Cft ^ 2 * N ^ 2 := by ring
    have h4 : Cft ^ 2 * N ^ 2 ≤ Cft ^ 2 * u :=
      mul_le_mul_of_nonneg_left hNu (sq_nonneg Cft)
    linarith
  have hftbU : covariantJetNormSq (I := I) (M := M) g 2
      (ricciCometricFourTraceCastG0 (I := I) g gU) ≤ 22 * Bft ^ 2 :=
    hftb U gU hUtie (hUn.trans hρb')
  have hkT2 : covariantJetNormSq (I := I) (M := M) g 2
      (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gT) ≤ Bk R * W := by
    rw [hW]
    exact hkerb gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have hkT1 : covariantJetNormSq (I := I) (M := M) g 1
      (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gT) ≤ Bk R * W :=
    le_trans (jet_mono_lip (I := I) (M := M) g (by norm_num : (1:ℕ) ≤ 2) _)
      hkT2
  have hkd : covariantJetNormSq (I := I) (M := M) g 1
      (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gT -
        ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gU) ≤ Bd R * (W * u) := by
    refine (hkerd gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU hδZ
      R A D2 hR hA hD2 hT2 hU2 hT3 hU3 hTU2).trans ?_
    rw [hW]
    have hBdR := hBd R hR
    have hstep : (1 + A + A ^ 2) ^ 4 * D2 ^ 2 ≤ (1 + A + A ^ 2) ^ 4 * u :=
      mul_le_mul_of_nonneg_left hDu (by positivity)
    exact mul_le_mul_of_nonneg_left hstep hBdR
  have hformT : ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gT =
      ccOperatorFieldComp (I := I) (M := M) g 2 4 2
        (ricciCometricFourTraceCastG0 (I := I) g gT)
        (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gT) := rfl
  have hformU : ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gU =
      ccOperatorFieldComp (I := I) (M := M) g 2 4 2
        (ricciCometricFourTraceCastG0 (I := I) g gU)
        (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gU) := rfl
  have hdel : ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gT -
        ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gU =
      ccOperatorFieldComp (I := I) (M := M) g 2 4 2
          (ricciCometricFourTraceCastG0 (I := I) g gT -
            ricciCometricFourTraceCastG0 (I := I) g gU)
          (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gT) +
        ccOperatorFieldComp (I := I) (M := M) g 2 4 2
          (ricciCometricFourTraceCastG0 (I := I) g gU)
          (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gT -
            ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gU) := by
    rw [hformT, hformU, operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
    module
  rw [hdel]
  have h1 : covariantJetNormSq (I := I) (M := M) g 1
      (ccOperatorFieldComp (I := I) (M := M) g 2 4 2
        (ricciCometricFourTraceCastG0 (I := I) g gT -
          ricciCometricFourTraceCastG0 (I := I) g gU)
        (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gT)) ≤ K1 R * (W * u) := by
    refine (happ _ _).trans ?_
    calc
      Ca * covariantJetNormSq (I := I) (M := M) g 2
            (ricciCometricFourTraceCastG0 (I := I) g gT -
              ricciCometricFourTraceCastG0 (I := I) g gU) *
          covariantJetNormSq (I := I) (M := M) g 1
            (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gT) ≤
          Ca * (22 * Cft ^ 2 * u) * (Bk R * W) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hftd hCa) hkT1
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCa (by positivity))
      _ = K1 R * (W * u) := by simp only [K1]; ring
  have h2 : covariantJetNormSq (I := I) (M := M) g 1
      (ccOperatorFieldComp (I := I) (M := M) g 2 4 2
        (ricciCometricFourTraceCastG0 (I := I) g gU)
        (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gT -
          ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gU)) ≤ K2 R * (W * u) := by
    refine (happ _ _).trans ?_
    calc
      Ca * covariantJetNormSq (I := I) (M := M) g 2
            (ricciCometricFourTraceCastG0 (I := I) g gU) *
          covariantJetNormSq (I := I) (M := M) g 1
            (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gT -
              ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gU) ≤
          Ca * (22 * Bft ^ 2) * (Bd R * (W * u)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hftbU hCa) hkd
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCa (by positivity))
      _ = K2 R * (W * u) := by simp only [K2]; ring
  refine (jet_add_lip (I := I) (M := M) g 1 _ _).trans ?_
  have hsum : 2 * (K1 R * (W * u) + K2 R * (W * u)) =
      B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
    simp only [B, hW, hu]
    ring
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g 2 4 2
            (ricciCometricFourTraceCastG0 (I := I) g gT -
              ricciCometricFourTraceCastG0 (I := I) g gU)
            (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gT)) +
        covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g 2 4 2
            (ricciCometricFourTraceCastG0 (I := I) g gU)
            (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gT -
              ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gU))) ≤
        2 * (K1 R * (W * u) + K2 R * (W * u)) := by linarith [h1, h2]
    _ = B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := hsum

private theorem ricciCovariantDerivativeConnectionDifference_pairing_firstOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (P Q : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_hQ : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g Q x u v =
            ccTensorBilin (I := I) g Q x v u)
        (_hPtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        (_hQtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδP : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (_hδQ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g Q) δ)
        (R A D2 N : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 Q ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 Q ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (P - Q) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 1
          (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gT P -
            RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gU Q) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
  obtain ⟨Kdag, hKdag, hdagb⟩ := dagLow_bdd_h2 (I := I) (M := M) hDim g
  obtain ⟨ρd, Cd, hρd, hCd, hdagd⟩ := dagLow_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨Cf034, hCf034, h034f⟩ :=
    app_h12_mul_lip (I := I) (M := M) hDim g 0 3 4
  obtain ⟨Ca034, hCa034, h034a⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 0 3 4
  obtain ⟨Cb034, hCb034, h034b⟩ :=
    app_h2_mul_lip (I := I) (M := M) hDim g 0 3 4
  obtain ⟨Kr1, hKr1, hrf1⟩ := decomposition_sobolev_one_lipschitz_bound (I := I) (M := M) hDim g
  obtain ⟨Kr2, hKr2, hrf2⟩ := decomposition_sobolev_two_lipschitz_bound (I := I) (M := M) hDim g
  obtain ⟨Cf222, hCf222, h222f⟩ :=
    app_h12_mul_lip (I := I) (M := M) hDim g 2 2 2
  obtain ⟨Ca222, hCa222, h222a⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 2 2 2
  obtain ⟨Be, hBe, hfsb⟩ :=
    RicciDeTurckLowOrder.exists_metricComparisonEndomorphism_slot_one_covariantJetNormSq_two_bound (I := I) (M := M) g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Be0, Be1, hBe0, hBe1, hfsd⟩ :=
    RicciDeTurckLowOrder.fullSlot_pair_h1 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let c1 : ℝ := 2 * (Cf034 * Cd + 2 * (Ca034 * Kdag))
  let c2 : ℝ := 2 * (Cb034 * Kdag)
  let D1 : ℝ → ℝ := fun R => Cf222 * Kr1 * c1 * Be R ^ 2
  let D2c : ℝ → ℝ := fun R =>
    Ca222 * Kr2 * c2 * (2 * Be0 R ^ 2 + 2 * Be1 R ^ 2)
  let B : ℝ → ℝ := fun R => 8 * (D1 R + D2c R)
  have hc10 : (0 : ℝ) ≤ c1 := by
    have e1 := mul_nonneg hCf034 hCd
    have e2 := mul_nonneg hCa034 hKdag
    simp only [c1]
    linarith only [e1, e2]
  have hc20 : (0 : ℝ) ≤ c2 := by
    have e1 := mul_nonneg hCb034 hKdag
    simp only [c2]
    linarith only [e1]
  have hD10 : ∀ R : ℝ, 0 ≤ D1 R := by
    intro R
    simp only [D1]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCf222 hKr1) hc10) (sq_nonneg _)
  have hD2c0 : ∀ R : ℝ, 0 ≤ D2c R := by
    intro R
    simp only [D2c]
    refine mul_nonneg (mul_nonneg (mul_nonneg hCa222 hKr2) hc20) ?_
    positivity
  refine ⟨ρd, B, hρd, ?_, ?_⟩
  · intro R hR
    have e1 := hD10 R
    have e2 := hD2c0 R
    simp only [B]
    linarith only [e1, e2]
  intro gT gU P Q hP hQ hPtie hQtie δ hδ_le hδ0 hδP hδQ
    R A D2 N hR hA hD2 hN hP2 hQ2 hP3 hQ3 hPQ2 hPn hQn hPQn
  set p : ℝ := 1 + A + A ^ 2 with hp
  have hp1 : (1 : ℝ) ≤ p := by
    rw [hp]; linarith only [hA, sq_nonneg A]
  have hp0 : (0 : ℝ) ≤ p := by linarith only [hp1]
  have hpA2 : A ^ 2 ≤ p := by
    rw [hp]; linarith only [hA]
  have hpm1 : (0 : ℝ) ≤ p - 1 := by linarith only [hp1]
  have hpq : (0 : ℝ) ≤ p ^ 2 + p + 1 := by
    linarith only [sq_nonneg p, hp0]
  have hp4_1 : p ≤ p ^ 4 := by
    linarith only [mul_nonneg (mul_nonneg hp0 hpm1) hpq]
  have hp4_3 : p ^ 3 ≤ p ^ 4 := by
    linarith only [mul_nonneg (mul_nonneg (mul_nonneg hp0 hp0) hp0) hpm1]
  set u : ℝ := D2 ^ 2 + N ^ 2 with hu
  have hu0 : (0 : ℝ) ≤ u := by
    rw [hu]; linarith only [sq_nonneg D2, sq_nonneg N]
  have hNu : N ^ 2 ≤ u := by rw [hu]; linarith only [sq_nonneg D2]
  have hDu : D2 ^ 2 ≤ u := by rw [hu]; linarith only [sq_nonneg N]
  have hpu0 : (0 : ℝ) ≤ p * u := mul_nonneg hp0 hu0
  have hpu : p * u ≤ p ^ 4 * u := mul_le_mul_of_nonneg_right hp4_1 hu0
  have hp3u : p ^ 3 * u ≤ p ^ 4 * u := mul_le_mul_of_nonneg_right hp4_3 hu0
  have huple : u ≤ p * u := by
    have h := mul_le_mul_of_nonneg_right hp1 hu0
    linarith only [h]
  set GT : SmoothCcTensor g 0 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 0 3 4
      (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT)
      (covGrad (I := I) (M := M) g 0 2 P) with hGT
  set GU : SmoothCcTensor g 0 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 0 3 4
      (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
      (covGrad (I := I) (M := M) g 0 2 Q) with hGU
  set ET : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gT) with hET
  set EU : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gU) with hEU
  have hdagU : covariantJetNormSq (I := I) (M := M) g 2
      (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU) ≤
      Kdag * (1 + A ^ 2) :=
    hdagb gU Q hQ hQtie hδ_le hδ0 hδQ A hA hQ3
  have hdagd' : covariantJetNormSq (I := I) (M := M) g 1
      (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT -
        RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU) ≤ Cd * N ^ 2 := by
    refine (hdagd P Q gT gU hPtie hQtie hPn hQn).trans ?_
    have hsq : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ^ 2 ≤
        N ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hPQn 2
    exact mul_le_mul_of_nonneg_left hsq hCd
  have hgP2 : covariantJetNormSq (I := I) (M := M) g 2
      (covGrad (I := I) (M := M) g 0 2 P) ≤ A ^ 2 :=
    (grad_h2_le_h3_lip (I := I) (M := M) g P).trans hP3
  have hgQ2 : covariantJetNormSq (I := I) (M := M) g 2
      (covGrad (I := I) (M := M) g 0 2 Q) ≤ A ^ 2 :=
    (grad_h2_le_h3_lip (I := I) (M := M) g Q).trans hQ3
  have hgd1 : covariantJetNormSq (I := I) (M := M) g 1
      (covGrad (I := I) (M := M) g 0 2 (P - Q)) ≤ D2 ^ 2 :=
    (grad_h1_le_h2_lip (I := I) (M := M) g (P - Q)).trans hPQ2
  have hGcomb : ccOperatorFieldComp (I := I) (M := M) g 0 3 4
        (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT -
          RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
        (covGrad (I := I) (M := M) g 0 2 P) +
      ccOperatorFieldComp (I := I) (M := M) g 0 3 4
        (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
        (covGrad (I := I) (M := M) g 0 2 (P - Q)) = GT - GU := by
    rw [hGT, hGU, operatorFieldComposition_sub_left, covGrad_sub, operatorFieldComposition_sub_right]
    module
  have hGd : covariantJetNormSq (I := I) (M := M) g 1 (GT - GU) ≤ c1 * (p * u) := by
    rw [← hGcomb]
    have e1 : covariantJetNormSq (I := I) (M := M) g 1
        (ccOperatorFieldComp (I := I) (M := M) g 0 3 4
          (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT -
            RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
          (covGrad (I := I) (M := M) g 0 2 P)) ≤
        Cf034 * Cd * (p * u) := by
      refine (h034f _ _).trans ?_
      have hstep : Cf034 * covariantJetNormSq (I := I) (M := M) g 1
            (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT -
              RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU) *
          covariantJetNormSq (I := I) (M := M) g 2
            (covGrad (I := I) (M := M) g 0 2 P) ≤
          Cf034 * (Cd * N ^ 2) * A ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hdagd' hCf034) hgP2
          (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCf034 (mul_nonneg hCd (sq_nonneg N)))
      refine hstep.trans ?_
      have hNA : N ^ 2 * A ^ 2 ≤ u * p :=
        mul_le_mul hNu hpA2 (sq_nonneg A) hu0
      have hmulc : Cf034 * Cd * (N ^ 2 * A ^ 2) ≤ Cf034 * Cd * (u * p) :=
        mul_le_mul_of_nonneg_left hNA (mul_nonneg hCf034 hCd)
      calc
        Cf034 * (Cd * N ^ 2) * A ^ 2 =
            Cf034 * Cd * (N ^ 2 * A ^ 2) := by ring
        _ ≤ Cf034 * Cd * (u * p) := hmulc
        _ = Cf034 * Cd * (p * u) := by ring
    have e2 : covariantJetNormSq (I := I) (M := M) g 1
        (ccOperatorFieldComp (I := I) (M := M) g 0 3 4
          (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
          (covGrad (I := I) (M := M) g 0 2 (P - Q))) ≤
        2 * (Ca034 * Kdag) * (p * u) := by
      refine (h034a _ _).trans ?_
      have hstep : Ca034 * covariantJetNormSq (I := I) (M := M) g 2
            (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU) *
          covariantJetNormSq (I := I) (M := M) g 1
            (covGrad (I := I) (M := M) g 0 2 (P - Q)) ≤
          Ca034 * (Kdag * (1 + A ^ 2)) * D2 ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hdagU hCa034) hgd1
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCa034 (mul_nonneg hKdag (by positivity)))
      refine hstep.trans ?_
      have h1 : (1 : ℝ) + A ^ 2 ≤ 2 * p := by linarith only [hp1, hpA2]
      have h2 : (1 + A ^ 2) * D2 ^ 2 ≤ 2 * p * D2 ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg D2)
      have h3 : 2 * p * D2 ^ 2 ≤ 2 * p * u :=
        mul_le_mul_of_nonneg_left hDu (by linarith only [hp0])
      have hAD : (1 + A ^ 2) * D2 ^ 2 ≤ 2 * (p * u) := by
        linarith only [h2, h3]
      have hmulc : Ca034 * Kdag * ((1 + A ^ 2) * D2 ^ 2) ≤
          Ca034 * Kdag * (2 * (p * u)) :=
        mul_le_mul_of_nonneg_left hAD (mul_nonneg hCa034 hKdag)
      calc
        Ca034 * (Kdag * (1 + A ^ 2)) * D2 ^ 2 =
            Ca034 * Kdag * ((1 + A ^ 2) * D2 ^ 2) := by ring
        _ ≤ Ca034 * Kdag * (2 * (p * u)) := hmulc
        _ = 2 * (Ca034 * Kdag) * (p * u) := by ring
    refine (jet_add_lip (I := I) (M := M) g 1 _ _).trans ?_
    simp only [c1]
    linarith only [e1, e2]
  have hGU2 : covariantJetNormSq (I := I) (M := M) g 2 GU ≤ c2 * p ^ 2 := by
    rw [hGU]
    refine (h034b _ _).trans ?_
    have hstep : Cb034 * covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU) *
        covariantJetNormSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g 0 2 Q) ≤
        Cb034 * (Kdag * (1 + A ^ 2)) * A ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hdagU hCb034) hgQ2
        (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
        (mul_nonneg hCb034 (mul_nonneg hKdag (by positivity)))
    refine hstep.trans ?_
    have h1 : (1 : ℝ) + A ^ 2 ≤ 2 * p := by linarith only [hp1, hpA2]
    have h2 : (1 + A ^ 2) * A ^ 2 ≤ 2 * p * A ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (sq_nonneg A)
    have h3 : 2 * p * A ^ 2 ≤ 2 * p * p :=
      mul_le_mul_of_nonneg_left hpA2 (by linarith only [hp0])
    have hAA : (1 + A ^ 2) * A ^ 2 ≤ 2 * p ^ 2 := by
      linarith only [h2, h3]
    have hmulc : Cb034 * Kdag * ((1 + A ^ 2) * A ^ 2) ≤
        Cb034 * Kdag * (2 * p ^ 2) :=
      mul_le_mul_of_nonneg_left hAA (mul_nonneg hCb034 hKdag)
    simp only [c2]
    calc
      Cb034 * (Kdag * (1 + A ^ 2)) * A ^ 2 =
          Cb034 * Kdag * ((1 + A ^ 2) * A ^ 2) := by ring
      _ ≤ Cb034 * Kdag * (2 * p ^ 2) := hmulc
      _ = 2 * (Cb034 * Kdag) * p ^ 2 := by ring
  have hETb : covariantJetNormSq (I := I) (M := M) g 2 ET ≤ Be R ^ 2 := by
    rw [hET]
    exact hfsb gT P hP hPtie hδ_le hδ0 hδP R hR hP2
  have hEd : covariantJetNormSq (I := I) (M := M) g 1 (ET - EU) ≤
      (2 * Be0 R ^ 2 + 2 * Be1 R ^ 2) * (p * u) := by
    rw [hET, hEU]
    refine (hfsd gT gU P Q hP hQ hPtie hQtie hδ_le hδ0 hδP hδ_le hδ0 hδQ
      R A D2 hR hA hD2 hQ2 hP3 hPQ2).trans ?_
    have hstep : (Be0 R * D2 + Be1 R * A * D2) ^ 2 ≤
        2 * Be0 R ^ 2 * D2 ^ 2 + 2 * Be1 R ^ 2 * (A ^ 2 * D2 ^ 2) := by
      linarith only [sq_nonneg (Be0 R * D2 - Be1 R * A * D2)]
    refine hstep.trans ?_
    have e1 : D2 ^ 2 ≤ p * u := by linarith only [hDu, huple]
    have e2 : A ^ 2 * D2 ^ 2 ≤ p * u :=
      mul_le_mul hpA2 hDu (sq_nonneg D2) hp0
    have f1 : 2 * Be0 R ^ 2 * D2 ^ 2 ≤ 2 * Be0 R ^ 2 * (p * u) :=
      mul_le_mul_of_nonneg_left e1 (by positivity)
    have f2 : 2 * Be1 R ^ 2 * (A ^ 2 * D2 ^ 2) ≤
        2 * Be1 R ^ 2 * (p * u) :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    linarith only [f1, f2]
  have hmono : ∀ σ : Equiv.Perm (Fin 4),
      covariantJetNormSq (I := I) (M := M) g 1
        (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT σ -
          RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU σ) ≤
        2 * (D1 R * (p * u) + D2c R * (p ^ 3 * u)) := by
    intro σ
    have hfT : RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT σ =
        ccOperatorFieldComp (I := I) (M := M) g 2 2 2
          (decompositionKernelContractionMonomialField (I := I) (M := M) g g GT σ)
          ET := by rw [hET]; rfl
    have hfU : RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU σ =
        ccOperatorFieldComp (I := I) (M := M) g 2 2 2
          (decompositionKernelContractionMonomialField (I := I) (M := M) g g GU σ)
          EU := by rw [hEU]; rfl
    have hsub : RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT σ -
          RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU σ =
        ccOperatorFieldComp (I := I) (M := M) g 2 2 2
            (decompositionKernelContractionMonomialField (I := I) (M := M) g g
              (GT - GU) σ) ET +
          ccOperatorFieldComp (I := I) (M := M) g 2 2 2
            (decompositionKernelContractionMonomialField (I := I) (M := M) g g GU σ)
            (ET - EU) := by
      rw [hfT, hfU, decomposition_sub_lipschitz_bound, operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
      module
    rw [hsub]
    have e1 : covariantJetNormSq (I := I) (M := M) g 1
        (ccOperatorFieldComp (I := I) (M := M) g 2 2 2
          (decompositionKernelContractionMonomialField (I := I) (M := M) g g
            (GT - GU) σ) ET) ≤ D1 R * (p * u) := by
      refine (h222f _ _).trans ?_
      have hr : covariantJetNormSq (I := I) (M := M) g 1
          (decompositionKernelContractionMonomialField (I := I) (M := M) g g
            (GT - GU) σ) ≤ Kr1 * (c1 * (p * u)) :=
        (hrf1 (GT - GU) σ).trans (mul_le_mul_of_nonneg_left hGd hKr1)
      have hstep : Cf222 * covariantJetNormSq (I := I) (M := M) g 1
            (decompositionKernelContractionMonomialField (I := I) (M := M) g g
              (GT - GU) σ) *
          covariantJetNormSq (I := I) (M := M) g 2 ET ≤
          Cf222 * (Kr1 * (c1 * (p * u))) * Be R ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hr hCf222) hETb
          (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCf222 (mul_nonneg hKr1 (mul_nonneg hc10 hpu0)))
      refine hstep.trans ?_
      simp only [D1]
      apply le_of_eq
      ring
    have e2 : covariantJetNormSq (I := I) (M := M) g 1
        (ccOperatorFieldComp (I := I) (M := M) g 2 2 2
          (decompositionKernelContractionMonomialField (I := I) (M := M) g g GU σ)
          (ET - EU)) ≤ D2c R * (p ^ 3 * u) := by
      refine (h222a _ _).trans ?_
      have hr : covariantJetNormSq (I := I) (M := M) g 2
          (decompositionKernelContractionMonomialField (I := I) (M := M) g g GU σ) ≤
          Kr2 * (c2 * p ^ 2) :=
        (hrf2 GU σ).trans (mul_le_mul_of_nonneg_left hGU2 hKr2)
      have hstep : Ca222 * covariantJetNormSq (I := I) (M := M) g 2
            (decompositionKernelContractionMonomialField (I := I) (M := M) g g
              GU σ) *
          covariantJetNormSq (I := I) (M := M) g 1 (ET - EU) ≤
          Ca222 * (Kr2 * (c2 * p ^ 2)) *
            ((2 * Be0 R ^ 2 + 2 * Be1 R ^ 2) * (p * u)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hr hCa222) hEd
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCa222
            (mul_nonneg hKr2 (mul_nonneg hc20 (sq_nonneg p))))
      refine hstep.trans ?_
      simp only [D2c]
      apply le_of_eq
      ring
    refine (jet_add_lip (I := I) (M := M) g 1 _ _).trans ?_
    linarith only [e1, e2]
  have hDAT : RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gT P =
      RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT
          RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation -
        RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT
          RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap := by
    rw [hGT]; rfl
  have hDAU : RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gU Q =
      RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU
          RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation -
        RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU
          RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap := by
    rw [hGU]; rfl
  have hsplit : RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gT P -
        RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gU Q =
      (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation -
          RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation) -
        (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap -
          RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap) := by
    rw [hDAT, hDAU]
    abel
  rw [hsplit]
  refine (jet_sub_lip (I := I) (M := M) g 1 _ _).trans ?_
  have hA' := hmono RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation
  have hB' := hmono RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap
  have hfold : D1 R * (p * u) + D2c R * (p ^ 3 * u) ≤
      (D1 R + D2c R) * (p ^ 4 * u) := by
    have e1 : D1 R * (p * u) ≤ D1 R * (p ^ 4 * u) :=
      mul_le_mul_of_nonneg_left hpu (hD10 R)
    have e2 : D2c R * (p ^ 3 * u) ≤ D2c R * (p ^ 4 * u) :=
      mul_le_mul_of_nonneg_left hp3u (hD2c0 R)
    have e3 : (D1 R + D2c R) * (p ^ 4 * u) =
        D1 R * (p ^ 4 * u) + D2c R * (p ^ 4 * u) := by ring
    rw [e3]
    exact add_le_add e1 e2
  have hlast : (8 : ℝ) * ((D1 R + D2c R) * (p ^ 4 * u)) =
      B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
    simp only [B, hp, hu]
    ring
  refine le_trans ?_ (le_of_eq hlast)
  linarith only [hA', hB', hfold]

private theorem good_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 N : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 1
          (RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) (s • T) -
            RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s) (s • U)) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
  obtain ⟨Ks, hKs, hsymm⟩ := inputSymm_h1 (I := I) (M := M) hDim g
  obtain ⟨ρA, BA, hρA, hBA, haa⟩ := ricciConnectionDifferenceQuadratic_pairing_firstOrder_bound (I := I) (M := M) hDim g
  obtain ⟨ρD, BD, hρD, hBD, hda⟩ := ricciCovariantDerivativeConnectionDifference_pairing_firstOrder_bound (I := I) (M := M) hDim g
  let B : ℝ → ℝ := fun R => Ks * (2 * (BA R + BD R))
  refine ⟨min ρA ρD, B, lt_min hρA hρD, ?_, ?_⟩
  · intro R hR
    have e1 := hBA R hR
    have e2 := hBD R hR
    simp only [B]
    positivity
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith only [hs.1, hs.2]
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [hcQ, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : covariantJetNormSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    rw [hcQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP3 : covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hQ3 : covariantJetNormSq (I := I) (M := M) g 3 Q ≤ A ^ 2 := by
    rw [hcQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 3) g U) hs2).trans hU3
  have hPQ2 : covariantJetNormSq (I := I) (M := M) g 2 (P - Q) ≤ D2 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by rw [hcP, hcQ, smul_sub]
    rw [hPQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g (T - U)) hs2).trans hTU2
  have hball : ∀ ρ' : ℝ, min ρA ρD ≤ ρ' →
      (‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ' ∧
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ') := by
    intro ρ' hρ'
    constructor
    · rw [hcP, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hTn.trans hρ'))
    · rw [hcQ, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hUn.trans hρ'))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have hPQ : P - Q = s • (T - U) := by rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  obtain ⟨hPnA, hQnA⟩ := hball ρA (min_le_left _ _)
  obtain ⟨hPnD, hQnD⟩ := hball ρD (min_le_right _ _)
  set Z : ℝ := (1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2) with hZ
  have hAA : covariantJetNormSq (I := I) (M := M) g 1
      (ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gmT -
        ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gmU) ≤ BA R * Z := by
    rw [hZ]
    exact haa gmT gmU P Q hPsymm hQsymm hPtie hQtie hδ_le hδ0 hδP hδQ hδZ
      R A D2 N hR hA hD2 hN hP2 hQ2 hP3 hQ3 hPQ2 hPnA hQnA hPQn
  have hDA : covariantJetNormSq (I := I) (M := M) g 1
      (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmT P -
        RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmU Q) ≤
      BD R * Z := by
    rw [hZ]
    exact hda gmT gmU P Q hPsymm hQsymm hPtie hQtie hδ_le hδ0 hδP hδQ
      R A D2 N hR hA hD2 hN hP2 hQ2 hP3 hQ3 hPQ2 hPnD hQnD hPQn
  have hlowT : RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmT P =
      ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gmT +
        RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmT P := rfl
  have hlowU : RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmU Q =
      ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gmU +
        RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmU Q := rfl
  have hgoodT : RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmT P =
      ccInputSlotSymm (I := I) (M := M) g
        (RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmT P) := rfl
  have hgoodU : RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmU Q =
      ccInputSlotSymm (I := I) (M := M) g
        (RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmU Q) := rfl
  have hlow : RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmT P -
        RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmU Q =
      (ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gmT -
          ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gmU) +
        (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmT P -
          RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmU Q) := by
    rw [hlowT, hlowU]
    abel
  have hgood : RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmT P -
        RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmU Q =
      ccInputSlotSymm (I := I) (M := M) g
        ((ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gmT -
            ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gmU) +
          (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmT P -
            RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmU Q)) := by
    rw [hgoodT, hgoodU, ccSymm_sub_lip, hlow]
  rw [hgood]
  have hZ0 : (0 : ℝ) ≤ Z := by rw [hZ]; positivity
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (ccInputSlotSymm (I := I) (M := M) g
          ((ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gmT -
              ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gmU) +
            (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmT P -
              RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmU Q))) ≤
        Ks * covariantJetNormSq (I := I) (M := M) g 1
          ((ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gmT -
              ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gmU) +
            (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmT P -
              RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmU Q)) :=
      hsymm _
    _ ≤ Ks * (2 * (covariantJetNormSq (I := I) (M := M) g 1
          (ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gmT -
            ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g gmU) +
        covariantJetNormSq (I := I) (M := M) g 1
          (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmT P -
            RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmU Q))) :=
      mul_le_mul_of_nonneg_left (jet_add_lip (I := I) (M := M) g 1 _ _) hKs
    _ ≤ Ks * (2 * (BA R * Z + BD R * Z)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add hAA hDA) (by norm_num)) hKs
    _ = B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
      simp only [B, hZ]
      ring

omit [SigmaCompactSpace M] in
private theorem selfLow_sub_parts
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (hU : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g U x u v =
        ccTensorBilin (I := I) g U x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
        g g T hδT hδZ s -
      RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
        g g U hδU hδZ s =
      (((((-2 : ℝ) •
            (RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g
                (metricPerturbationPath (I := I) g T 0 hδT hδZ s) (s • T) -
              RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g
                (metricPerturbationPath (I := I) g U 0 hδU hδZ s) (s • U)) +
          ((deTurckLieCovariantDerivativeTermField (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδT hδZ
              lieDecompositionQ lieDecompositionEps s) -
          (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g U hδU hδZ
              lieDecompositionQ lieDecompositionEps s))) +
        (lieCorrectionZeroVectorBundle (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδT hδZ s) -
          lieCorrectionZeroVectorBundle (I := I) (M := M) g
            (metricPerturbationPath (I := I) g U 0 hδU hδZ s))) +
        (lieCorrectionZeroMixedConnection (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g -
          lieCorrectionZeroMixedConnection (I := I) (M := M) g
            (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g)) +
        (lieCorrectionZeroRiemann (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδT hδZ s) -
          lieCorrectionZeroRiemann (I := I) (M := M) g
            (metricPerturbationPath (I := I) g U 0 hδU hδZ s))) := by
  rw [selfLow_parts (I := I) (M := M) g T hT hδ_lt hδT hδZ hs,
    selfLow_parts (I := I) (M := M) g U hU hδ_lt hδU hδZ hs]
  dsimp only
  module

private theorem selfLow_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 N : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 1
          (RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
              g g T hδT hδZ s -
            RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
              g g U hδU hδZ s) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
  obtain ⟨ρg, Background, hρg, hBackground, hgood⟩ :=
    good_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨ρl, Bl, hρl, hBl, hlie⟩ :=
    lieCov_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨ρv, Bv, hρv, hBv, hvb⟩ :=
    vb_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨ρa, Ba, hρa, hBa, hamix⟩ :=
    amix_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨ρr, Cr, hρr, hCr, hriem⟩ :=
    riem_pair_h1 (I := I) (M := M) hDim g
  set ρ : ℝ := min (min ρg ρl) (min ρv (min ρa ρr)) with hρdef
  have hρ0 : 0 < ρ :=
    lt_min (lt_min hρg hρl) (lt_min hρv (lt_min hρa hρr))
  let B : ℝ → ℝ := fun R =>
    64 * Background R + 16 * Bl R + 8 * Bv R + 4 * Ba R + 2 * Cr ^ 2
  refine ⟨ρ, B, hρ0, ?_, ?_⟩
  · intro R hR
    have h1 := hBackground R hR
    have h2 := hBl R hR
    have h3 := hBv R hR
    have h4 := hBa R hR
    have h5 : (0 : ℝ) ≤ Cr ^ 2 := sq_nonneg _
    simp only [B]
    positivity
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hρc : ρ ≤ ρg ∧ ρ ≤ ρl ∧ ρ ≤ ρv ∧ ρ ≤ ρa ∧ ρ ≤ ρr := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      · rw [hρdef]
        first
        | exact le_trans (min_le_left _ _) (min_le_left _ _)
        | exact le_trans (min_le_left _ _) (min_le_right _ _)
        | exact le_trans (min_le_right _ _) (min_le_left _ _)
        | exact le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _))
        | exact le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_right _ _))
  have hXg := hgood T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2
    (hTn.trans hρc.1) (hUn.trans hρc.1) hTUn hs
  have hXl := hlie T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2
    (hTn.trans hρc.2.1) (hUn.trans hρc.2.1) hTUn hs
  have hXv := hvb T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2
    (hTn.trans hρc.2.2.1) (hUn.trans hρc.2.2.1) hTUn hs
  have hXa := hamix T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2
    (hTn.trans hρc.2.2.2.1) (hUn.trans hρc.2.2.2.1) hTUn hs
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρr := by
    rw [hcP, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using (hTn.trans hρc.2.2.2.2))
  have hQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρr := by
    rw [hcQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using (hUn.trans hρc.2.2.2.2))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤
      N := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  have hpl1 : (1 : ℝ) ≤ (1 + A + A ^ 2) ^ 4 := by
    have hb1 : (1 : ℝ) ≤ 1 + A + A ^ 2 := by
      calc
        (1 : ℝ) ≤ 1 + A := le_add_of_nonneg_right hA
        _ ≤ 1 + A + A ^ 2 := le_add_of_nonneg_right (sq_nonneg A)
    calc (1 : ℝ) = 1 ^ 4 := by norm_num
      _ ≤ (1 + A + A ^ 2) ^ 4 :=
        pow_le_pow_left₀ zero_le_one hb1 4
  have hXr : covariantJetNormSq (I := I) (M := M) g 1
      (lieCorrectionZeroRiemann (I := I) (M := M) g gmT -
        lieCorrectionZeroRiemann (I := I) (M := M) g gmU) ≤
      Cr ^ 2 * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
    refine (hriem P Q gmT gmU hPtie hQtie hPn hQn).trans ?_
    have h1 : Cr * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖ ≤ Cr * N :=
      mul_le_mul_of_nonneg_left hPQn hCr
    have h2 : (Cr * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖) ^ 2 ≤ (Cr * N) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hCr (norm_nonneg _)) h1 2
    refine h2.trans ?_
    have hN2 : (Cr * N) ^ 2 = Cr ^ 2 * N ^ 2 := by ring
    rw [hN2]
    have hstep : N ^ 2 ≤ (1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2) := by
      calc
        N ^ 2 ≤ D2 ^ 2 + N ^ 2 := le_add_of_nonneg_left (sq_nonneg D2)
        _ = 1 * (D2 ^ 2 + N ^ 2) := (one_mul _).symm
        _ ≤ (1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2) :=
          mul_le_mul_of_nonneg_right hpl1
            (add_nonneg (sq_nonneg D2) (sq_nonneg N))
    exact mul_le_mul_of_nonneg_left hstep (sq_nonneg _)
  rw [selfLow_sub_parts (I := I) (M := M) g T U hT hU
    hδ_lt hδT hδU hδZ hs]
  set Y1 : SmoothCcTensor g 2 2 :=
    (-2 : ℝ) •
      (RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmT P -
        RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmU Q)
    with hY1
  set Y2 : SmoothCcTensor g 2 2 :=
    (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gmT g -
        deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδT hδZ
          lieDecompositionQ lieDecompositionEps s) -
      (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gmU g -
        deTurckLieTopOrderPairingFamily (I := I) (M := M) g U hδU hδZ
          lieDecompositionQ lieDecompositionEps s) with hY2
  set Y3 : SmoothCcTensor g 2 2 :=
    lieCorrectionZeroVectorBundle (I := I) (M := M) g gmT -
      lieCorrectionZeroVectorBundle (I := I) (M := M) g gmU with hY3
  set Y4 : SmoothCcTensor g 2 2 :=
    lieCorrectionZeroMixedConnection (I := I) (M := M) g gmT g -
      lieCorrectionZeroMixedConnection (I := I) (M := M) g gmU g with hY4
  set Y5 : SmoothCcTensor g 2 2 :=
    lieCorrectionZeroRiemann (I := I) (M := M) g gmT -
      lieCorrectionZeroRiemann (I := I) (M := M) g gmU with hY5
  set X : ℝ := (1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2) with hX
  have hX0 : 0 ≤ X := by
    rw [hX]
    positivity
  have hj1 : covariantJetNormSq (I := I) (M := M) g 1 Y1 ≤ 4 * (Background R * X) := by
    rw [hY1]
    rw [jet_smul_lip]
    have h4 : ((-2 : ℝ)) ^ 2 = 4 := by norm_num
    rw [h4]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hXg (by norm_num : (0 : ℝ) ≤ 4)
  have hj2 : covariantJetNormSq (I := I) (M := M) g 1 Y2 ≤ Bl R * X := by
    rw [hY2]
    exact hXl
  have hj3 : covariantJetNormSq (I := I) (M := M) g 1 Y3 ≤ Bv R * X := by
    rw [hY3]
    exact hXv
  have hj4 : covariantJetNormSq (I := I) (M := M) g 1 Y4 ≤ Ba R * X := by
    rw [hY4]
    exact hXa
  have hj5 : covariantJetNormSq (I := I) (M := M) g 1 Y5 ≤ Cr ^ 2 * X := by
    rw [hY5]
    exact hXr
  have h12 : covariantJetNormSq (I := I) (M := M) g 1 (Y1 + Y2) ≤
      2 * (4 * (Background R * X) + Bl R * X) := by
    have hadd := jet_add_lip (I := I) (M := M) g 1 Y1 Y2
    exact hadd.trans
      (mul_le_mul_of_nonneg_left (add_le_add hj1 hj2) (by norm_num))
  have h123 : covariantJetNormSq (I := I) (M := M) g 1 ((Y1 + Y2) + Y3) ≤
      2 * (2 * (4 * (Background R * X) + Bl R * X) + Bv R * X) := by
    have hadd := jet_add_lip (I := I) (M := M) g 1 (Y1 + Y2) Y3
    exact hadd.trans
      (mul_le_mul_of_nonneg_left (add_le_add h12 hj3) (by norm_num))
  have h1234 : covariantJetNormSq (I := I) (M := M) g 1 (((Y1 + Y2) + Y3) + Y4) ≤
      2 * (2 * (2 * (4 * (Background R * X) + Bl R * X) + Bv R * X) +
        Ba R * X) := by
    have hadd := jet_add_lip (I := I) (M := M) g 1 ((Y1 + Y2) + Y3) Y4
    exact hadd.trans
      (mul_le_mul_of_nonneg_left (add_le_add h123 hj4) (by norm_num))
  calc
    covariantJetNormSq (I := I) (M := M) g 1 ((((Y1 + Y2) + Y3) + Y4) + Y5) ≤
      2 * (covariantJetNormSq (I := I) (M := M) g 1 (((Y1 + Y2) + Y3) + Y4) +
        covariantJetNormSq (I := I) (M := M) g 1 Y5) :=
      jet_add_lip (I := I) (M := M) g 1 _ _
    _ ≤ 2 * (2 * (2 * (2 * (4 * (Background R * X) + Bl R * X) + Bv R * X) +
        Ba R * X) + Cr ^ 2 * X) := by
      exact mul_le_mul_of_nonneg_left (add_le_add h1234 hj5) (by norm_num)
    _ = B R * X := by
      simp only [B]
      ring

theorem zeroOrderCoefficientDifference_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 N : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 1
          (ricciDeTurckLowOrderDifference (I := I) (M := M) g T U
            (lt_of_le_of_lt hδ_le
              (by norm_num : (1 : ℝ) / 3 < 1))
            hδT hδU hδZ) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
  obtain ⟨ρ, Bs, hρ, hBs, hker⟩ :=
    selfLow_pair_h1 (I := I) (M := M) hDim g
  refine ⟨ρ, Bs, hρ, hBs, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn
  let hδ_lt : δ < 1 :=
    lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  let Φ : ℝ → SmoothCcTensor g 2 2 := fun s =>
    RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
        g g T hδT hδZ s -
      RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
        g g U hδU hδZ s
  let S : Set ℝ := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    dsimp only [S]
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hjoint :=
    covariantJetJoint_sub (I := I) (M := M) g _ _
      (RicciDeTurckLowOrder.selfLow_joint
        (I := I) (M := M) g g T hδT hδZ)
      (RicciDeTurckLowOrder.selfLow_joint
        (I := I) (M := M) g g U hδU hδZ)
  set X : ℝ := (1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2) with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    positivity
  set Btot : ℝ := Real.sqrt (Bs R * X) with hBtot
  have hB0 : 0 ≤ Btot := Real.sqrt_nonneg _
  have hBsq : Btot ^ 2 = Bs R * X := by
    rw [hBtot]
    exact Real.sq_sqrt (mul_nonneg (hBs R hR) hX0)
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      covariantJetNormSq (I := I) (M := M) g 1 (Φ s) ≤ Btot ^ 2 := by
    intro s hs
    rw [hBsq]
    have := hker T U hT hU hδ_le hδ0 hδT hδU hδZ
      R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn hs
    rw [← hXdef] at this
    exact this
  have hpath := path_jetL2_le (I := I) (M := M)
    g 2 2 1 Φ S metricPerturbationPathDomain_isOpen hSI hjoint
    (B := Btot)
    (by
      intro t ht
      simpa only [covariantJetNormSq, Nat.reduceAdd] using hpoint t ht)
  have hfin : covariantJetNormSq (I := I) (M := M) g 1
      (ricciDeTurckLowOrderDifference (I := I) (M := M) g T U hδ_lt hδT hδU hδZ) ≤
      Btot ^ 2 := by
    simpa only [covariantJetNormSq, ricciDeTurckLowOrderDifference, Φ, S, Nat.reduceAdd] using hpath
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (ricciDeTurckLowOrderDifference (I := I) (M := M) g T U
          (lt_of_le_of_lt hδ_le
            (by norm_num : (1 : ℝ) / 3 < 1))
          hδT hδU hδZ) ≤ Btot ^ 2 := hfin
    _ = Bs R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
      rw [hBsq, hXdef]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem grad_shift_lip
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    covariantJetNormSq (I := I) (M := M) g 1
        (iteratedCovGrad (I := I) g 0 2 1 W) ≤
      covariantJetNormSq (I := I) (M := M) g 2 W := by
  have hcomp : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g 0 3 i
          (iteratedCovGrad (I := I) g 0 2 1 W)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g 0 2 (1 + i) W‖ ^ 2 := by
    intro i
    rw [SmoothCcTensor.norm_def (I := I) (M := M),
      SmoothCcTensor.norm_def (I := I) (M := M),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g 0 (3 + i)
        (iteratedCovGrad (I := I) g 0 3 i
          (iteratedCovGrad (I := I) g 0 2 1 W)),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g 0 (2 + (1 + i))
        (iteratedCovGrad (I := I) g 0 2 (1 + i) W)]
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun x => ?_))
    exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g 0 2 1 i W x
  have h0 : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g 0 2 0 W‖ ^ 2 :=
    sq_nonneg _
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (iteratedCovGrad (I := I) g 0 2 1 W) =
      ‖iteratedCovGrad (I := I) g 0 3 0
          (iteratedCovGrad (I := I) g 0 2 1 W)‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g 0 3 1
          (iteratedCovGrad (I := I) g 0 2 1 W)‖ ^ 2 := by
      simp only [covariantJetNormSq, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add]
    _ = ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g 0 2 2 W‖ ^ 2 := by
      rw [hcomp 0, hcomp 1]
    _ ≤ ‖iteratedCovGrad (I := I) g 0 2 0 W‖ ^ 2 +
        (‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g 0 2 2 W‖ ^ 2) := by
      exact le_add_of_nonneg_left h0
    _ = covariantJetNormSq (I := I) (M := M) g 2 W := by
      simp only [covariantJetNormSq, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add]
      ring

theorem firstOrderCoefficientDifference_lowAction_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ C : ℝ, ∃ Bq : ℝ → ℝ, ∃ B0 B1 : ℝ,
      0 < ρ ∧ 0 ≤ C ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ Bq R) ∧
      0 ≤ B0 ∧ 0 ≤ B1 ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ W : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
          ((lowerScaleDiff (I := I) (M := M) g T U
              (lt_of_le_of_lt hδ_le
                (by norm_num : (1 : ℝ) / 3 < 1))
              hδT hδU hδZ).firstOrderAction (I := I) (M := M) W)‖ ≤
        C * Real.sqrt
            (Bq R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) +
              (B0 * D3 + B1 * N + B1 * A * N) ^ 2) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ := by
  obtain ⟨ρ0, Bq0, hρ0, hBq0, hc0⟩ :=
    zeroOrderCoefficientDifference_tame (I := I) (M := M) hDim g
  obtain ⟨ρ1, B0c, B1c, hρ1, hB0c, hB1c, hc1⟩ :=
    firstOrderCoefficientDifference_tame (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ12⟩ :=
    app_h12_mul_lip (I := I) (M := M) hDim g 0 2 2
  obtain ⟨Cb, hCb, happ21⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 0 3 2
  obtain ⟨Cs, hCs, hspec⟩ :=
    exists_firstOrderAction_secondToFirstOrder_spectralSobolev_bound (I := I) (M := M) g
  set ρ : ℝ := min ρ0 ρ1 with hρdef
  have hρpos : 0 < ρ := lt_min hρ0 hρ1
  set K : ℝ := 2 * Ca + 2 * Cb with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact add_nonneg (mul_nonneg (by norm_num) hCa) (mul_nonneg (by norm_num) hCb)
  let Bq : ℝ → ℝ := fun R => K * Bq0 R
  let B0 : ℝ := Real.sqrt K * B0c
  let B1 : ℝ := Real.sqrt K * B1c
  have hB0' : 0 ≤ B0 := mul_nonneg (Real.sqrt_nonneg _) hB0c
  have hB1' : 0 ≤ B1 := mul_nonneg (Real.sqrt_nonneg _) hB1c
  refine ⟨ρ, Cs, Bq, B0, B1, hρpos, hCs,
    fun R hR => mul_nonneg hK0 (hBq0 R hR), hB0', hB1', ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 D3 N hR hA hD2 hD3 hN hT2 hU2 hT3 hU3 hTU2 hTU3 hTn hUn hTUn W
  have hM0 := hc0 T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2
    (hTn.trans (min_le_left _ _)) (hUn.trans (min_le_left _ _)) hTUn
  have hM1 := hc1 T U hT hU hδ_le hδ0 hδT hδU hδZ
    (hTn.trans (min_le_right _ _)) (hUn.trans (min_le_right _ _))
    A D3 hA hD3 hT3 hTU3
  set X : ℝ := (1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2) with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    positivity
  set Nrm : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
    with hNrm
  set M1 : ℝ := (B0c * D3 + B1c * Nrm + B1c * A * Nrm) ^ 2 with hM1def
  have hM1n : 0 ≤ M1 := sq_nonneg _
  set Q : ℝ := K * (Bq0 R * X + M1) with hQdef
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    exact mul_nonneg hK0
      (add_nonneg (mul_nonneg (hBq0 R hR) hX0) hM1n)
  set D : LowerScaleActionCoefficients g :=
    lowerScaleDiff (I := I) (M := M) g T U
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
      hδT hδU hδZ with hDdef
  have hcore : ∀ V : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 1
          (D.firstOrderAction (I := I) (M := M) V) ≤
        Q * covariantJetNormSq (I := I) (M := M) g 2 V := by
    intro V
    have hC0eq : D.zeroOrderCoefficient = ricciDeTurckLowOrderDifference (I := I) (M := M) g T U
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        hδT hδU hδZ := by
      rw [hDdef]
      exact lowerScaleDifference_zeroOrderCoefficient (I := I) (M := M) g T U _ hδT hδU hδZ
    have hC1eq : D.firstOrderCoefficient = firstOrderCoefficientDifference (I := I) (M := M) g T U
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        hδT hδU hδZ := by
      rw [hDdef]
      exact lowerScaleDifference_firstOrderCoefficient (I := I) (M := M) g T U _ hδT hδU hδZ
    have hj0 : covariantJetNormSq (I := I) (M := M) g 1 D.zeroOrderCoefficient ≤ Bq0 R * X := by
      rw [hC0eq]
      exact hM0
    have hj1 : covariantJetNormSq (I := I) (M := M) g 2 D.firstOrderCoefficient ≤ M1 := by
      rw [hC1eq]
      exact hM1
    have ha1 : D.firstOrderAction (I := I) (M := M) V =
        operatorFieldApply (I := I) (M := M) g 2 2 D.zeroOrderCoefficient V +
          operatorFieldApply (I := I) (M := M) g 3 2 D.firstOrderCoefficient
            (iteratedCovGrad (I := I) g 0 2 1 V) := rfl
    rw [ha1]
    have hL : covariantJetNormSq (I := I) (M := M) g 1
        (operatorFieldApply (I := I) (M := M) g 2 2 D.zeroOrderCoefficient V) ≤
        Ca * (Bq0 R * X) * covariantJetNormSq (I := I) (M := M) g 2 V := by
      have h := happ12 D.zeroOrderCoefficient V
      rw [operatorFieldComposition_zero_eq_operatorFieldApply] at h
      refine h.trans ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hj0 hCa)
        (jet_nonneg_lip (I := I) (M := M) (m := 2) g V)
    have hRt : covariantJetNormSq (I := I) (M := M) g 1
        (operatorFieldApply (I := I) (M := M) g 3 2 D.firstOrderCoefficient
          (iteratedCovGrad (I := I) g 0 2 1 V)) ≤
        Cb * M1 * covariantJetNormSq (I := I) (M := M) g 2 V := by
      have h := happ21 D.firstOrderCoefficient (iteratedCovGrad (I := I) g 0 2 1 V)
      rw [operatorFieldComposition_zero_eq_operatorFieldApply] at h
      refine h.trans
        (mul_le_mul
          (mul_le_mul_of_nonneg_left hj1 hCb)
          (grad_shift_lip (I := I) (M := M) g V)
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCb hM1n))
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (operatorFieldApply (I := I) (M := M) g 2 2 D.zeroOrderCoefficient V +
            operatorFieldApply (I := I) (M := M) g 3 2 D.firstOrderCoefficient
              (iteratedCovGrad (I := I) g 0 2 1 V)) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 1
            (operatorFieldApply (I := I) (M := M) g 2 2 D.zeroOrderCoefficient V) +
          covariantJetNormSq (I := I) (M := M) g 1
            (operatorFieldApply (I := I) (M := M) g 3 2 D.firstOrderCoefficient
              (iteratedCovGrad (I := I) g 0 2 1 V))) :=
        jet_add_lip (I := I) (M := M) g 1 _ _
      _ ≤ 2 * (Ca * (Bq0 R * X) * covariantJetNormSq (I := I) (M := M) g 2 V +
          Cb * M1 * covariantJetNormSq (I := I) (M := M) g 2 V) := by
        exact mul_le_mul_of_nonneg_left (add_le_add hL hRt) (by norm_num)
      _ ≤ Q * covariantJetNormSq (I := I) (M := M) g 2 V := by
        rw [hQdef, hKdef]
        have hjV := jet_nonneg_lip (I := I) (M := M) (m := 2) g V
        have hp : 0 ≤ Bq0 R * X := mul_nonneg (hBq0 R hR) hX0
        have hsum : Ca * (Bq0 R * X) + Cb * M1 ≤
            (Ca + Cb) * (Bq0 R * X + M1) := by
          calc
            Ca * (Bq0 R * X) + Cb * M1 ≤
                Ca * (Bq0 R * X) + Cb * M1 +
                  (Ca * M1 + Cb * (Bq0 R * X)) :=
              le_add_of_nonneg_right
                (add_nonneg (mul_nonneg hCa hM1n) (mul_nonneg hCb hp))
            _ = (Ca + Cb) * (Bq0 R * X + M1) := by ring
        calc
          2 * (Ca * (Bq0 R * X) * covariantJetNormSq (I := I) (M := M) g 2 V +
              Cb * M1 * covariantJetNormSq (I := I) (M := M) g 2 V) =
              2 * (Ca * (Bq0 R * X) + Cb * M1) *
                covariantJetNormSq (I := I) (M := M) g 2 V := by ring
          _ ≤ 2 * ((Ca + Cb) * (Bq0 R * X + M1)) *
                covariantJetNormSq (I := I) (M := M) g 2 V :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsum (by norm_num)) hjV
          _ = (2 * Ca + 2 * Cb) * (Bq0 R * X + M1) *
                covariantJetNormSq (I := I) (M := M) g 2 V := by ring
  have hfin := hspec D Q hQ0 hcore W
  refine hfin.trans ?_
  have hQle : Real.sqrt Q ≤ Real.sqrt
      (Bq R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) +
        (B0 * D3 + B1 * N + B1 * A * N) ^ 2) := by
    apply Real.sqrt_le_sqrt
    rw [hQdef]
    have hKsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK0
    have hexp : (B0 * D3 + B1 * N + B1 * A * N) ^ 2 =
        K * (B0c * D3 + B1c * N + B1c * A * N) ^ 2 := by
      simp only [B0, B1]
      rw [show (Real.sqrt K * B0c * D3 + Real.sqrt K * B1c * N +
          Real.sqrt K * B1c * A * N) ^ 2 =
          Real.sqrt K ^ 2 *
            (B0c * D3 + B1c * N + B1c * A * N) ^ 2 from by ring,
        hKsq]
    have hM1le : M1 ≤ (B0c * D3 + B1c * N + B1c * A * N) ^ 2 := by
      rw [hM1def]
      have hle : B0c * D3 + B1c * Nrm + B1c * A * Nrm ≤
          B0c * D3 + B1c * N + B1c * A * N := by
        have h1 : B1c * Nrm ≤ B1c * N :=
          mul_le_mul_of_nonneg_left (by rw [hNrm]; exact hTUn) hB1c
        have h2 : B1c * A * Nrm ≤ B1c * A * N :=
          mul_le_mul_of_nonneg_left (by rw [hNrm]; exact hTUn)
            (mul_nonneg hB1c hA)
        exact add_le_add (add_le_add le_rfl h1) h2
      have hnn : 0 ≤ B0c * D3 + B1c * Nrm + B1c * A * Nrm := by
        have : 0 ≤ Nrm := by rw [hNrm]; exact norm_nonneg _
        have h1 : 0 ≤ B0c * D3 := mul_nonneg hB0c hD3
        have h2 : 0 ≤ B1c * Nrm := mul_nonneg hB1c this
        have h3 : 0 ≤ B1c * A * Nrm :=
          mul_nonneg (mul_nonneg hB1c hA) this
        exact add_nonneg (add_nonneg h1 h2) h3
      exact pow_le_pow_left₀ hnn hle 2
    simp only [Bq]
    rw [hexp, ← hXdef]
    calc
      K * (Bq0 R * X + M1) = K * (Bq0 R * X) + K * M1 := mul_add _ _ _
      _ ≤ K * (Bq0 R * X) +
          K * (B0c * D3 + B1c * N + B1c * A * N) ^ 2 :=
        add_le_add_right (mul_le_mul_of_nonneg_left hM1le hK0) _
      _ = K * Bq0 R * X +
          K * (B0c * D3 + B1c * N + B1c * A * N) ^ 2 := by ring
  calc
    Cs * Real.sqrt Q *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ ≤
      Cs * Real.sqrt
          (Bq R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) +
            (B0 * D3 + B1 * N + B1 * A * N) ^ 2) *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hQle hCs) (norm_nonneg _)

theorem metricCorrection_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 D3 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g T -
            metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨C, hC, hpair⟩ :=
    metricCorrection_pair (I := I) (M := M) hDim g
  obtain ⟨Bs, hBs, hself⟩ :=
    wXi_self_tame (I := I) (M := M) hDim g
  obtain ⟨W0, W1, hW0, hW1, hw⟩ :=
    exists_metricLoweredConnectionDifference_covariantJetNormSq_two_sub_tame_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let H : ℝ := Real.sqrt C
  let B0 : ℝ → ℝ := fun R => H * R * W0 R
  let B1 : ℝ → ℝ := fun R => H * (Bs R + R * W1 R)
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hHsq : H ^ 2 = C := by
    simpa only [H] using Real.sq_sqrt hC
  refine ⟨B0, B1, ?_, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg (mul_nonneg hH hR) (hW0 R hR)
  · intro R hR
    exact mul_nonneg hH
      (add_nonneg (hBs R hR) (mul_nonneg hR (hW1 R hR)))
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0
    hδT hδU hδZ R A D2 D3 hR hA hD2 hD3
    hT2 hU2 hT3 hTU2 hTU3
  let WT : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (metricLoweredConnectionDifference (I := I) (M := M) g gT g)
  let WD : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (metricLoweredConnectionDifference (I := I) (M := M) g gT g -
      metricLoweredConnectionDifference (I := I) (M := M) g gU g)
  let X : ℝ := W0 R * D3 + W1 R * D2 + W1 R * A * D2
  let S : ℝ := Bs R * A * D2
  let Y : ℝ := R * X
  have hWT : WT ≤ (Bs R * A) ^ 2 := by
    simpa only [WT] using hself gT T hT hTtie
      hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have hWD : WD ≤ X ^ 2 := by
    simpa only [WD, X] using
      hw gT gU g T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have hWT0 : 0 ≤ WT := jet_nonneg_lip (I := I) (M := M) g _
  have hWD0 : 0 ≤ WD := jet_nonneg_lip (I := I) (M := M) g _
  have hX0 : 0 ≤ X :=
    add_nonneg
      (add_nonneg (mul_nonneg (hW0 R hR) hD3)
        (mul_nonneg (hW1 R hR) hD2))
      (mul_nonneg (mul_nonneg (hW1 R hR) hA) hD2)
  have hS0 : 0 ≤ S :=
    mul_nonneg (mul_nonneg (hBs R hR) hA) hD2
  have hY0 : 0 ≤ Y := mul_nonneg hR hX0
  have hfirst :
      covariantJetNormSq (I := I) (M := M) g 2 (T - U) * WT ≤ S ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (T - U) * WT ≤
          D2 ^ 2 * (Bs R * A) ^ 2 :=
        mul_le_mul hTU2 hWT hWT0 (sq_nonneg D2)
      _ = S ^ 2 := by
        simp only [S]
        ring
  have hsecond :
      covariantJetNormSq (I := I) (M := M) g 2 U * WD ≤ Y ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 U * WD ≤
          R ^ 2 * X ^ 2 :=
        mul_le_mul hU2 hWD hWD0 (sq_nonneg R)
      _ = Y ^ 2 := by
        simp only [Y]
        ring
  have hraw := hpair gT gU g T U
  change covariantJetNormSq (I := I) (M := M) g 2
      (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g T -
        metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U) ≤
    C * (covariantJetNormSq (I := I) (M := M) g 2 (T - U) * WT +
      covariantJetNormSq (I := I) (M := M) g 2 U * WD) at hraw
  have hCSY :
      C * (covariantJetNormSq (I := I) (M := M) g 2 (T - U) * WT +
          covariantJetNormSq (I := I) (M := M) g 2 U * WD) ≤
        C * (S ^ 2 + Y ^ 2) :=
    mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hC
  have hquad :
      C * (S ^ 2 + Y ^ 2) ≤ (H * S + H * Y) ^ 2 := by
    rw [show C * (S ^ 2 + Y ^ 2) =
        (H * S) ^ 2 + (H * Y) ^ 2 by
      rw [← hHsq]
      ring]
    nlinarith only [mul_nonneg (mul_nonneg hH hS0) (mul_nonneg hH hY0)]
  have hlin :
      H * S + H * Y ≤
        B0 R * D3 + B1 R * D2 + B1 R * A * D2 := by
    have hextra : 0 ≤ H * Bs R * D2 :=
      mul_nonneg (mul_nonneg hH (hBs R hR)) hD2
    simp only [S, Y, X, B0, B1]
    nlinarith only [hextra]
  have hlin0 : 0 ≤ H * S + H * Y :=
    add_nonneg (mul_nonneg hH hS0) (mul_nonneg hH hY0)
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g T -
          metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U) ≤
      C * (covariantJetNormSq (I := I) (M := M) g 2 (T - U) * WT +
        covariantJetNormSq (I := I) (M := M) g 2 U * WD) := hraw
    _ ≤ C * (S ^ 2 + Y ^ 2) := hCSY
    _ ≤ (H * S + H * Y) ^ 2 := hquad
    _ ≤ (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 :=
      pow_le_pow_left₀ hlin0 hlin 2

theorem metricCorrection_tame_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 1
          (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g T -
            metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U) ≤
        (B0 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨C, hC, hpair⟩ :=
    metricCorrection_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨Bs, hBs, hself⟩ :=
    wXi_self_tame (I := I) (M := M) hDim g
  obtain ⟨W0, W1, hW0, hW1, hw⟩ :=
    exists_metricLoweredConnectionDifference_covariantJetNormSq_one_sub_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let H : ℝ := Real.sqrt C
  let B0 : ℝ → ℝ := fun R => H * R * W0 R
  let B1 : ℝ → ℝ := fun R => H * (Bs R + R * W1 R)
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hHsq : H ^ 2 = C := by
    simpa only [H] using Real.sq_sqrt hC
  refine ⟨B0, B1, ?_, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg (mul_nonneg hH hR) (hW0 R hR)
  · intro R hR
    exact mul_nonneg hH
      (add_nonneg (hBs R hR) (mul_nonneg hR (hW1 R hR)))
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0
    hδT hδU hδZ R A D2 hR hA hD2 hT2 hU2 hT3 hTU2
  let WT : ℝ := covariantJetNormSq (I := I) (M := M) g 1
    (metricLoweredConnectionDifference (I := I) (M := M) g gT g)
  let WD : ℝ := covariantJetNormSq (I := I) (M := M) g 1
    (metricLoweredConnectionDifference (I := I) (M := M) g gT g -
      metricLoweredConnectionDifference (I := I) (M := M) g gU g)
  let X : ℝ := W0 R * D2 + W1 R * A * D2
  let S : ℝ := Bs R * A * D2
  let Y : ℝ := R * X
  have hWT2 :
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g) ≤
        (Bs R * A) ^ 2 := by
    exact hself gT T hT hTtie
      hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have hWT : WT ≤ (Bs R * A) ^ 2 := by
    exact (jet_mono_lip (I := I) (M := M) g
      (by omega : 1 ≤ 2)
      (metricLoweredConnectionDifference (I := I) (M := M) g gT g)).trans hWT2
  have hWD : WD ≤ X ^ 2 := by
    simpa only [WD, X] using
      hw gT gU g T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R A D2 hR hA hD2 hU2 hT3 hTU2
  have hWT0 : 0 ≤ WT := jet_nonneg_lip (I := I) (M := M) g _
  have hWD0 : 0 ≤ WD := jet_nonneg_lip (I := I) (M := M) g _
  have hX0 : 0 ≤ X :=
    add_nonneg
      (mul_nonneg (hW0 R hR) hD2)
      (mul_nonneg (mul_nonneg (hW1 R hR) hA) hD2)
  have hS0 : 0 ≤ S :=
    mul_nonneg (mul_nonneg (hBs R hR) hA) hD2
  have hY0 : 0 ≤ Y := mul_nonneg hR hX0
  have hfirst :
      covariantJetNormSq (I := I) (M := M) g 2 (T - U) * WT ≤ S ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (T - U) * WT ≤
          D2 ^ 2 * (Bs R * A) ^ 2 :=
        mul_le_mul hTU2 hWT hWT0 (sq_nonneg D2)
      _ = S ^ 2 := by
        simp only [S]
        ring
  have hsecond :
      covariantJetNormSq (I := I) (M := M) g 2 U * WD ≤ Y ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 U * WD ≤
          R ^ 2 * X ^ 2 :=
        mul_le_mul hU2 hWD hWD0 (sq_nonneg R)
      _ = Y ^ 2 := by
        simp only [Y]
        ring
  have hraw := hpair gT gU T U
  change covariantJetNormSq (I := I) (M := M) g 1
      (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g T -
        metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U) ≤
    C * (covariantJetNormSq (I := I) (M := M) g 2 (T - U) * WT +
      covariantJetNormSq (I := I) (M := M) g 2 U * WD) at hraw
  have hCSY :
      C * (covariantJetNormSq (I := I) (M := M) g 2 (T - U) * WT +
          covariantJetNormSq (I := I) (M := M) g 2 U * WD) ≤
        C * (S ^ 2 + Y ^ 2) :=
    mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hC
  have hquad :
      C * (S ^ 2 + Y ^ 2) ≤ (H * S + H * Y) ^ 2 := by
    rw [show C * (S ^ 2 + Y ^ 2) =
        (H * S) ^ 2 + (H * Y) ^ 2 by
      rw [← hHsq]
      ring]
    nlinarith only [mul_nonneg (mul_nonneg hH hS0) (mul_nonneg hH hY0)]
  have hlin :
      H * S + H * Y = B0 R * D2 + B1 R * A * D2 := by
    simp only [S, Y, X, B0, B1]
    ring
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g T -
          metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U) ≤
      C * (covariantJetNormSq (I := I) (M := M) g 2 (T - U) * WT +
        covariantJetNormSq (I := I) (M := M) g 2 U * WD) := hraw
    _ ≤ C * (S ^ 2 + Y ^ 2) := hCSY
    _ ≤ (H * S + H * Y) ^ 2 := hquad
    _ = (B0 R * D2 + B1 R * A * D2) ^ 2 := by rw [hlin]

private theorem first_order_action_sobolev_extensions_commute_local
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowerScaleActionCoefficients g) :
    (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
          (A.firstOrderActionThirdToSecondOrder (I := I) (M := M)) =
      (A.firstOrderActionSecondToFirstOrder (I := I) (M := M)).comp
        (tensorHsInclusion (I := I) (M := M) (g := g)
          (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)) := by
  obtain ⟨_, _, hpair⟩ := exists_firstOrderAction_spectralSobolev_extensions (I := I) (M := M) g
  obtain ⟨Ch, hCh, hhigh⟩ :=
    exists_lowerScaleFirstOrderAction_thirdToSecondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨Cl, hCl, hlow⟩ :=
    exists_lowerScaleFirstOrderAction_secondToFirstOrder_bound (I := I) (M := M) hDim g
  let J : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient +
      covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient
  let B : ℝ := Real.sqrt J
  let C : ℝ := Ch + Cl
  let Q : ℝ := (C * B) ^ 2
  have hJ : 0 ≤ J := by
    exact add_nonneg
      (jet_nonneg_lip (I := I) (M := M) g A.zeroOrderCoefficient)
      (jet_nonneg_lip (I := I) (M := M) g A.firstOrderCoefficient)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = J := by
    simpa only [B] using Real.sq_sqrt hJ
  have hC : 0 ≤ C := add_nonneg hCh hCl
  have hQ : 0 ≤ Q := sq_nonneg _
  have hcoeff :
      covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient +
          covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient ≤ B ^ 2 := by
    rw [hBsq]
  have hHi : ∀ W : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 2
          (A.firstOrderAction (I := I) (M := M) W) ≤
        Q * covariantJetNormSq (I := I) (M := M) g 3 W := by
    intro W
    let D : ℝ :=
      Real.sqrt (covariantJetNormSq (I := I) (M := M) g 3 W)
    have hW : 0 ≤ covariantJetNormSq (I := I) (M := M) g 3 W :=
      jet_nonneg_lip (I := I) (M := M) g W
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDsq :
        D ^ 2 = covariantJetNormSq (I := I) (M := M) g 3 W := by
      simpa only [D] using Real.sq_sqrt hW
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (A.firstOrderAction (I := I) (M := M) W) ≤
        (Ch * B * D) ^ 2 :=
          hhigh A W B D hB hD hcoeff (by rw [hDsq])
      _ ≤ (C * B * D) ^ 2 := by
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCh hB) hD)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right hCl) hB) hD) 2
      _ = Q * covariantJetNormSq (I := I) (M := M) g 3 W := by
        rw [show (C * B * D) ^ 2 = (C * B) ^ 2 * D ^ 2 by ring,
          hDsq]
  have hLo : ∀ W : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 1
          (A.firstOrderAction (I := I) (M := M) W) ≤
        Q * covariantJetNormSq (I := I) (M := M) g 2 W := by
    intro W
    let D : ℝ :=
      Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 W)
    have hW : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 W :=
      jet_nonneg_lip (I := I) (M := M) g W
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDsq :
        D ^ 2 = covariantJetNormSq (I := I) (M := M) g 2 W := by
      simpa only [D] using Real.sq_sqrt hW
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (A.firstOrderAction (I := I) (M := M) W) ≤
        (Cl * B * D) ^ 2 :=
          hlow A W B D hB hD hcoeff (by rw [hDsq])
      _ ≤ (C * B * D) ^ 2 := by
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCl hB) hD)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_left hCh) hB) hD) 2
      _ = Q * covariantJetNormSq (I := I) (M := M) g 2 W := by
        rw [show (C * B * D) ^ 2 = (C * B) ^ 2 * D ^ 2 by ring,
          hDsq]
  exact (hpair A Q hQ hHi hLo).2.2.2.2

theorem firstOrderAction_difference_sobolev_extensions_commute
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (A B : LowerScaleActionCoefficients g) :
    (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
          (A.firstOrderActionThirdToSecondOrder (I := I) (M := M) -
            B.firstOrderActionThirdToSecondOrder (I := I) (M := M)) =
      (A.firstOrderActionSecondToFirstOrder (I := I) (M := M) -
          B.firstOrderActionSecondToFirstOrder (I := I) (M := M)).comp
        (tensorHsInclusion (I := I) (M := M) (g := g)
          (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)) := by
  have hA := first_order_action_sobolev_extensions_commute_local (I := I) (M := M) hDim g A
  have hB := first_order_action_sobolev_extensions_commute_local (I := I) (M := M) hDim g B
  apply ContinuousLinearMap.ext
  intro W
  have hAW := congrArg (fun L => L W) hA
  have hBW := congrArg (fun L => L W) hB
  simp only [ContinuousLinearMap.comp_apply] at hAW hBW
  simp only [ContinuousLinearMap.comp_apply,
    sub_apply, map_sub]
  rw [hAW, hBW]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem firstOrderAction_subtract
    (g : SmoothRiemannianMetric I M)
    (A B : LowerScaleActionCoefficients g) (T U : SmoothCcTensor g 0 2) :
    A.firstOrderAction (I := I) (M := M) T - B.firstOrderAction (I := I) (M := M) U =
      A.firstOrderAction (I := I) (M := M) (T - U) +
        (A.firstOrderCoefficientDifference B).firstOrderAction
          (I := I) (M := M) U := by
  simp only [LowerScaleActionCoefficients.firstOrderAction, LowerScaleActionCoefficients.firstOrderCoefficientDifference,
    iteratedCovGrad_sub, operatorFieldApplication_sub_left, app_sub_right]
  module

theorem lowResidual_sub
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    (hU : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g U x v w =
        ccTensorBilin (I := I) g U x w v)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (R A : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hT2 : covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2)
    (hU2 : covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2)
    (hT3 : covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2)
    (hU3 : covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2) :
    let hδ_lt : δ < 1 :=
      lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
    let LT : LowerScaleActionCoefficients g :=
      lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδT hδZ
    lowerScaleResidual (I := I) (M := M) g T hδ_lt hδT hδZ -
        lowerScaleResidual (I := I) (M := M) g U hδ_lt hδU hδZ =
      LT.firstOrderAction (I := I) (M := M) (T - U) +
        (lowerScaleDiff (I := I) (M := M) g T U
          hδ_lt hδT hδU hδZ).firstOrderAction (I := I) (M := M) U := by
  obtain ⟨_, _, hdiag⟩ :=
    exists_lowerScaleResidual_secondOrder_bound (I := I) (M := M) hDim g
  dsimp only
  have hT_eq :=
    (hdiag T hT hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3).1
  have hU_eq :=
    (hdiag U hU hδ_le hδ0 hδU hδZ R A hR hA hU2 hU3).1
  rw [hT_eq, hU_eq]
  exact firstOrderAction_subtract (I := I) (M := M) g
    (lowerScaleActionCoefficients (I := I) (M := M) g g T
      (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ)
    (lowerScaleActionCoefficients (I := I) (M := M) g g U
      (lt_of_le_of_lt hδ_le (by norm_num)) hδU hδZ) T U

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
