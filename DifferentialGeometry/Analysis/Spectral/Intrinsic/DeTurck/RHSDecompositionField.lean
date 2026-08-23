import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricDiffJoint
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSZeroDecomposition
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFieldsBackgroundDifferenceDecomposition
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBoundCoeffFieldOrderZeroIdentities

noncomputable section

set_option backward.isDefEq.respectTransparency false

open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
      [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem bilin_smul
    (g : SmoothRiemannianMetric I M) (a : Real)
    (A : SmoothCcTensor g 0 2) (x : M)
    (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g (a • A) x v w =
      a * ccTensorBilin (I := I) g A x v w := by
  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem perturb_eq_diff
    (g g1 : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    (htie : ∀ (x : M) (v w : TangentSpace I x),
      g1.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g P x v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g P x v w =
        ccTensorBilin (I := I) g P x w v) :
    P = metricDifferenceCcTensor (I := I) (M := M) g g1 := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun slots => ?_)
  have hslots : slots = ![slots 0, slots 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hslots, unitModel_eq_ccTensorBilin_local, metricDiff_unit]
  change
    ccTensorBilin (I := I) g P x (slots 0) (slots 1) =
      g1.inner x (slots 0) (slots 1) - g.inner x (slots 0) (slots 1)
  rw [htie x (slots 0) (slots 1), ccTensorBilinSymm_apply,
    hPsymm x (slots 0) (slots 1)]
  ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem cc22_ext_app
    (g : SmoothRiemannianMetric I M) (C D : SmoothCcTensor g 2 2)
    (h : ∀ W : SmoothCcTensor g 0 2,
      operatorFieldApply (I := I) (M := M) g 2 2 C W =
        operatorFieldApply (I := I) (M := M) g 2 2 D W) :
    C = D := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  refine tensorRSSpace_ext 2 2 x (fun u => ?_)
  let V : TensorRSSpace 0 2 I x :=
    (show TensorRSSpace 0 2 I x from
      ((MixedSection.eval₀ (F := E) (E := TangentSpace I) x).smulRight u))
  obtain ⟨sigmaW, hsigmaW⟩ := ContMDiffSection.exists_eq_at
    (I := I) (n := (⊤ : ℕ∞)) (F := TensorRSModel 0 2 Real E)
    (V := fun y : M => TensorRSSpace 0 2 I y) x V
  let W : SmoothCcTensor g 0 2 :=
    { toSection := sigmaW
      hasCompactSupport := HasCompactSupport.of_compactSpace _ }
  have happ : (operatorFieldApply (I := I) (M := M) g 2 2 C W).toSection x =
      (operatorFieldApply (I := I) (M := M) g 2 2 D W).toSection x := by
    rw [h W]
  have happ' :
      (show Tensor0SSpace 2 I x →L[Real] Tensor0SSpace 2 I x
          from C.toSection x)
          ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 2 I x
            from W.toSection x) (unitTensor (I := I) (M := M) x)) =
        (show Tensor0SSpace 2 I x →L[Real] Tensor0SSpace 2 I x
          from D.toSection x)
          ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 2 I x
            from W.toSection x) (unitTensor (I := I) (M := M) x)) := by
    exact congrArg
      (fun T : TensorRSSpace 0 2 I x =>
        (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 2 I x from T)
          (unitTensor (I := I) (M := M) x))
      happ
  have hW :
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 2 I x
          from W.toSection x) (unitTensor (I := I) (M := M) x) = u := by
    rw [show W.toSection x = V from hsigmaW]
    change
      ((MixedSection.eval₀ (F := E) (E := TangentSpace I) x).smulRight u)
          (ContinuousMultilinearMap.constOfIsEmpty Real
            (fun _ : Fin 0 => TangentSpace I x) 1) = u
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rw [hW] at happ'
  exact happ'

private theorem halfRiem_decomposition
    (g g1 : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    (htie : ∀ (x : M) (v w : TangentSpace I x),
      g1.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g P x v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g P x v w =
        ccTensorBilin (I := I) g P x w v) :
    (1 / 2 : Real) •
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g g1 -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g g) =
      ricciArmOrder0AACommCoeffField (I := I) (M := M) g g1 +
        backgroundRicciCommutatorDiffDecompositionRemainderField (I := I) (M := M) g g1 +
        decompositionKernelContractionField (I := I) (M := M) g g1
          (iteratedCovGrad (I := I) g 0 2 2 P)
          (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 := by
  classical
  have hP := perturb_eq_diff (I := I) (M := M) g g1 P htie hPsymm
  rw [hP]
  refine cc22_ext_app (I := I) (M := M) g _ _ (fun W => ?_)
  have hprim :=
    ricciArmOrder0RiemannHalfBackgroundDiff_operatorFieldApplication_eq_residualFieldSum_add_decompositionKernelSecondGrad
      (I := I) (M := M) g g1 P htie hPsymm W
  rw [hP] at hprim
  simpa only [operatorFieldApplication_smul_left, operatorFieldApplication_sub_left, operatorFieldApplication_add_left,
    backgroundRicciCommutatorDiffDecompositionRemainderField,
    operatorFieldApplication_decompositionKernelContractionField] using hprim

theorem ricciDecomposition_eq
    (g g1 : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    (htie : ∀ (x : M) (v w : TangentSpace I x),
      g1.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g P x v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g P x v w =
        ccTensorBilin (I := I) g P x w v) :
    (-2 : Real) • ricciPalatiniHalfCoefficient (I := I) (M := M) g g1 +
        ricciDecomposition0 (I := I) (M := M) g g1 P =
      (-2 : Real) •
          linearizedRicciConnectionDifferenceOrder0CoeffField (I := I) (M := M) g g1 -
        (2 : Real) •
          decompositionKernelContractionField (I := I) (M := M) g g1
            (iteratedCovGrad (I := I) g 0 2 2 P)
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 := by
  have hP := perturb_eq_diff (I := I) (M := M) g g1 P htie hPsymm
  have hhalf := halfRiem_decomposition (I := I) (M := M) g g1 P htie hPsymm
  have htwice :
      ricciArmOrder0RiemannCoeff (I := I) (M := M) g g1 -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g g =
        (2 : Real) • ((1 / 2 : Real) •
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g g1 -
            ricciArmOrder0RiemannCoeff (I := I) (M := M) g g)) := by
    rw [smul_smul, show (2 : Real) * (1 / 2) = 1 by norm_num, one_smul]
  rw [hhalf] at htwice
  rw [sub_eq_iff_eq_add] at htwice
  rw [ricciPalatiniHalfCoefficient, ricciDecomposition0]
  rw [show
      ccOperatorFieldComp (I := I) (M := M) g 2 2 2
          (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g g1 -
            ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g g)
          (ccSlotSwapField (I := I) (M := M) g) +
        (1 / 2 : Real) •
          ricciArmSharpGradKoszulResidualField (I := I) (M := M) g g1 P -
        ricciArmRicciFoldRemainderField (I := I) (M := M) g g1 P =
      backgroundRicciCommutatorDiffDecompositionRemainderField (I := I) (M := M) g g1 by
        rw [hP]
        rfl]
  rw [htwice]
  module

theorem rhsDecomposition_eq
    (g g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) delta)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    (hdelta_lt : delta < 1) (s : Real) (hs : s ∈ Set.Icc (0 : Real) 1) :
    rhsDecomposition0 (I := I) (M := M) g g_bg T hdelta hdeltaZ s =
      (-2 : Real) •
          linearizedRicciConnectionDifferenceOrder0CoeffField (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) -
        (2 : Real) •
          decompositionKernelContractionField (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s)
            (iteratedCovGrad (I := I) g 0 2 2 (s • T))
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 +
        deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) g_bg +
        deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) g_bg +
        lieCorrectionZeroField (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) g_bg -
        deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hdelta hdeltaZ
          lieDecompositionQ lieDecompositionEps s := by
  let P : SmoothCcTensor g 0 2 := s • T
  let g1 : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := delta) (δ' := delta) :=
    Icc_subset_metricPerturbationPathDomain hdelta_lt hdelta_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g1.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g P y v w := by
    intro y v w
    rw [← show convexPerturbation (I := I) g T 0 s = P by
      rw [convexPerturbation, smul_zero, zero_add]]
    exact metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hdelta hdeltaZ hs_mem y v w
  have hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g P x v w =
        ccTensorBilin (I := I) g P x w v := by
    intro x v w
    dsimp only [P]
    rw [bilin_smul (I := I) (M := M),
      bilin_smul (I := I) (M := M), hTsymm x v w]
  have hlie :
      deTurckLieCovariantDerivativeArmField (I := I) (M := M) g g1 g_bg +
          deTurckLieEndoArmField (I := I) (M := M) g g1 g_bg =
        deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g g1 g_bg +
          deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g g1 g_bg := by
    rw [← deTurckLieCoeffField_eq_covDerivArm_add_endoArm,
      deTurckLieConnectionDifferenceDerivCoeffField_add_deTurckLieCovariantDerivativeInsertionField]
  rw [rhsDecomposition0]
  rw [ricciDecomposition_eq (I := I) (M := M) g g1 P htie hPsymm]
  rw [lieDecomposition0]
  change
    (-2 : Real) •
          linearizedRicciConnectionDifferenceOrder0CoeffField (I := I) (M := M) g g1 -
        (2 : Real) •
          decompositionKernelContractionField (I := I) (M := M) g g1
            (iteratedCovGrad (I := I) g 0 2 2 P)
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 +
        (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g g1 g_bg -
          deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hdelta hdeltaZ
            lieDecompositionQ lieDecompositionEps s +
          deTurckLieEndoArmField (I := I) (M := M) g g1 g_bg +
          lieCorrectionZeroField (I := I) (M := M) g g1 g_bg) =
      (-2 : Real) •
          linearizedRicciConnectionDifferenceOrder0CoeffField (I := I) (M := M) g g1 -
        (2 : Real) •
          decompositionKernelContractionField (I := I) (M := M) g g1
            (iteratedCovGrad (I := I) g 0 2 2 P)
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 +
        deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g g1 g_bg +
        deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g g1 g_bg +
        lieCorrectionZeroField (I := I) (M := M) g g1 g_bg -
        deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hdelta hdeltaZ
          lieDecompositionQ lieDecompositionEps s
  rw [show
    deTurckLieCovariantDerivativeArmField (I := I) (M := M) g g1 g_bg -
          deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hdelta hdeltaZ
            lieDecompositionQ lieDecompositionEps s +
          deTurckLieEndoArmField (I := I) (M := M) g g1 g_bg +
          lieCorrectionZeroField (I := I) (M := M) g g1 g_bg =
        (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g g1 g_bg +
          deTurckLieEndoArmField (I := I) (M := M) g g1 g_bg) +
          lieCorrectionZeroField (I := I) (M := M) g g1 g_bg -
          deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hdelta hdeltaZ
            lieDecompositionQ lieDecompositionEps s by module, hlie]
  module

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
