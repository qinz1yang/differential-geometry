import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrectionZeroCore
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniDecomposition
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold Topology ContDiff Matrix

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open LieCorrectionZeroCore

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def lieCorrectionZeroInsertion (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g_bg x))
      contMDiff_toFun := lieCorrectionZeroInsertionFib_contMDiff (I := I) g₀ g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

def lieCorrectionZeroVectorBundle (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (lieCorrectionZeroVBFib (I := I) g₀ g₁ x))
      contMDiff_toFun := lieCorrectionZeroVBFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

def lieCorrectionZeroMixedConnection (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (lieCorrectionZeroMixedConnectionFib (I := I) g₀ g₁ g_bg x))
      contMDiff_toFun := lieCorrectionZeroMixedConnectionFib_contMDiff (I := I) g₀ g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

def lieCorrectionZeroRiemann (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (lieCorrectionZeroRiemFib (I := I) g₀ g₁ x))
      contMDiff_toFun := lieCorrectionZeroRiemFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)]
  [CompactSpace M]
  [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem nEndo_base (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    lieCorrectionZeroNEndo (I := I) g₀ g₁ g₀ x =
      -deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x := by
  rw [lieCorrectionZeroNEndo, sub_self, zero_sub]

omit [NeZero (Module.finrank ℝ E)]
  [CompactSpace M]
  [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem nEndo_diff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x -
        lieCorrectionZeroNEndo (I := I) g₀ g₁ g₀ x =
      PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
            ∀ b : M, TangentSpace I b) x) -
        PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg :
            ∀ b : M, TangentSpace I b) x) := by
  rw [nEndo_base (I := I) (M := M) g₀ g₁ x, lieCorrectionZeroNEndo]
  abel

omit [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] in
theorem insert_base (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg +
        deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g₀ =
      lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg -
        lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  change Tensor0SSpace.toModel
        (lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g_bg x D) m +
      Tensor0SSpace.toModel
        (deTurckLieCovariantDerivativeInsertionFib (I := I) g₁ g₀ x D) m =
    Tensor0SSpace.toModel
        (lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g_bg x D) m -
      Tensor0SSpace.toModel
        (lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g₀ x D) m
  rw [lieCorrectionZeroInsertionFib_toModel (I := I) g₀ g₁ g_bg x D m,
    lieCorrectionZeroInsertionFib_toModel (I := I) g₀ g₁ g₀ x D m,
    deTurckLieCovariantDerivativeInsertionFib_toModel (I := I) g₁ g₀ x D m]
  have hN0 : ∀ v : TangentSpace I x,
      lieCorrectionZeroNEndo (I := I) g₀ g₁ g₀ x v =
        -(deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x v) := by
    intro v
    simpa using congrArg
      (fun A : TangentSpace I x →L[ℝ] TangentSpace I x => A v)
      (nEndo_base (I := I) (M := M) g₀ g₁ x)
  have e0 : Tensor0SSpace.toModel D
      (Function.update m 0 (lieCorrectionZeroNEndo (I := I) g₀ g₁ g₀ x (m 0))) =
      -(Tensor0SSpace.toModel D
        (Function.update m 0 (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x (m 0)))) := by
    rw [hN0 (m 0), show (-(deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x (m 0))) =
        ((-1 : ℝ) • (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x (m 0))) from
          (neg_one_smul ℝ _).symm]
    rw [ContinuousMultilinearMap.map_update_smul, neg_one_smul]
  have e1 : Tensor0SSpace.toModel D
      (Function.update m 1 (lieCorrectionZeroNEndo (I := I) g₀ g₁ g₀ x (m 1))) =
      -(Tensor0SSpace.toModel D
        (Function.update m 1 (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x (m 1)))) := by
    rw [hN0 (m 1), show (-(deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x (m 1))) =
        ((-1 : ℝ) • (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x (m 1))) from
          (neg_one_smul ℝ _).symm]
    rw [ContinuousMultilinearMap.map_update_smul, neg_one_smul]
  rw [e0, e1]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem lieCorrectionZero_decomp (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lieCorrectionZeroField (I := I) (M := M) g₀ g₁ g_bg =
      ((lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg +
          lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁) +
        lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg) +
      lieCorrectionZeroRiemann (I := I) (M := M) g₀ g₁ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  change TensorRSSpace.ofCLM
      (lieCorrectionZeroTotalFib (I := I) g₀ g₁ g_bg x) = _
  rw [lieCorrectionZeroTotalFib]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem tail_base_split (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lieCorrectionZeroField (I := I) (M := M) g₀ g₁ g_bg +
        deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g₀ =
      (((lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg -
            lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀) +
          lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁) +
        lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg) +
      lieCorrectionZeroRiemann (I := I) (M := M) g₀ g₁ := by
  rw [lieCorrectionZero_decomp (I := I) (M := M) g₀ g₁ g_bg]
  rw [← insert_base (I := I) (M := M) g₀ g₁ g_bg]
  abel

end DifferentialGeometry.Analysis.Spectral

end
