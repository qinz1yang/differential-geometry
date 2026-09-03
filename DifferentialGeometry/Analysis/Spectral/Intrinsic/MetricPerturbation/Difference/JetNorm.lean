import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricPerturbation.Difference.TensorFields
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.TensorRSContRiemannianBundle
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

attribute [local instance]
  pointwiseModelDualNormedAddCommGroup
  pointwiseModelDualNormedSpace
  pointwiseModelBilinearNormedAddCommGroup
  pointwiseModelBilinearNormedSpace
  pointwiseModelTrilinearNormedAddCommGroup
  pointwiseModelTrilinearNormedSpace
  pointwiseModelQuadrilinearNormedAddCommGroup
  pointwiseModelQuadrilinearNormedSpace
  pointwiseTangentDualNormedAddCommGroup
  pointwiseTangentDualNormedSpace
  pointwiseTangentBilinearNormedAddCommGroup
  pointwiseTangentBilinearNormedSpace
  pointwiseTangentTrilinearNormedAddCommGroup
  pointwiseTangentTrilinearNormedSpace
  pointwiseTangentTrilinearAddCommGroup
  pointwiseTangentTrilinearModule
  pointwiseTangentTrilinearSMul
  pointwiseTangentTrilinearTopology
  pointwiseSectionAddCommGroup
  pointwiseSectionModule
  pointwiseTangentQuadrilinearNormedAddCommGroup
  pointwiseTangentQuadrilinearNormedSpace
  pointwiseTangentQuadrilinearAddCommGroup
  pointwiseTangentQuadrilinearModule
  pointwiseTangentBilinearAddCommGroup
  pointwiseTangentBilinearModule
  pointwiseBilinearSectionAddCommGroup
  pointwiseBilinearSectionModule
  pointwiseTensor0SModelNormedAddCommGroup
  pointwiseTensor0SModelNormedSpace
  pointwiseTensorRSModelNormedAddCommGroup
  pointwiseTensorRSModelNormedSpace
  pointwiseTensor01TotalSpaceTopology
  pointwiseTensor01FiberBundle
  pointwiseTensor01VectorBundle
  pointwiseTensor01ContMDiffVectorBundle
  pointwiseTensor02TotalSpaceTopology
  pointwiseIteratedTensor02FiberBundle
  pointwiseIteratedTensor02VectorBundle
  pointwiseIteratedTensor02ContMDiffVectorBundle
  pointwiseTensor03TotalSpaceTopology
  pointwiseTensor03FiberBundle
  pointwiseTensor03VectorBundle
  pointwiseTensor03ContMDiffVectorBundle
  pointwiseTensor04TotalSpaceTopology
  pointwiseTensor04FiberBundle
  pointwiseTensor04VectorBundle
  pointwiseTensor04ContMDiffVectorBundle
  pointwiseTensorRSTotalSpaceTopology
  pointwiseTensorRSFiberBundle

private local instance metricDifferenceJetNormTensorRSNormedAddCommGroup
    (r s : ℕ) [Bundle.RiemannianBundle (fun y : M => TensorRSSpace r s I y)] (x : M) :
    NormedAddCommGroup (TensorRSSpace r s I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TensorRSSpace r s I y) x

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem continuous_riemannian_fiber_norm_of_continuous_section
    {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
    {V₀ : M → Type*} [∀ x, NormedAddCommGroup (V₀ x)] [∀ x, InnerProductSpace ℝ (V₀ x)]
    [TopologicalSpace (TotalSpace F₀ V₀)] [FiberBundle F₀ V₀] [VectorBundle ℝ F₀ V₀]
    [IsContinuousRiemannianBundle F₀ V₀]
    {σ : Π x : M, V₀ x}
    (hσ : Continuous (fun x : M => TotalSpace.mk' F₀ (E := V₀) x (σ x))) :
    Continuous (fun x : M => ‖σ x‖) := by
  have h_inner : Continuous (fun x : M => (inner ℝ (σ x) (σ x) : ℝ)) :=
    Continuous.inner_bundle (F := F₀) (E := V₀) hσ hσ
  have h_eq : (fun x : M => ‖σ x‖) = fun x : M => Real.sqrt (inner ℝ (σ x) (σ x)) := by
    funext x
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [h_eq]
  exact Real.continuous_sqrt.comp h_inner

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Bundle.continuousMultilinearMap.mixedInstNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixedInstNormedSpace
  Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
def metricDifference2JetNorm (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) : ℝ :=
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 2
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 3
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 4 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 4
  ‖metricDifference02MixedSection (I := I) g₁ g₂ x‖
    + ‖metricDifference02CovMixedSection (I := I) g₀ g₁ g₂ x‖
    + ‖metricDifference02CovIterateMixedSection (I := I) g₀ g₁ g₂ x‖

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Bundle.continuousMultilinearMap.mixedInstNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixedInstNormedSpace
  Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricDifference2JetNorm_eq_riemannianNorm_sum
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 2
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 3
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 4 I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 4
    metricDifference2JetNorm (I := I) g₀ g₁ g₂ x =
      ‖metricDifference02MixedSection (I := I) g₁ g₂ x‖
        + ‖metricDifference02CovMixedSection (I := I) g₀ g₁ g₂ x‖
        + ‖metricDifference02CovIterateMixedSection (I := I) g₀ g₁ g₂ x‖ :=
  rfl

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Bundle.continuousMultilinearMap.mixedInstNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixedInstNormedSpace
  Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricDifference2JetNorm_nonneg
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    0 ≤ metricDifference2JetNorm (I := I) g₀ g₁ g₂ x := by
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 2
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 3
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 4 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 4
  rw [metricDifference2JetNorm_eq_riemannianNorm_sum (I := I) g₀ g₁ g₂ x]
  exact add_nonneg
    (add_nonneg
      (norm_nonneg (metricDifference02MixedSection (I := I) g₁ g₂ x))
      (norm_nonneg (metricDifference02CovMixedSection (I := I) g₀ g₁ g₂ x)))
    (norm_nonneg (metricDifference02CovIterateMixedSection (I := I) g₀ g₁ g₂ x))

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Bundle.continuousMultilinearMap.mixedInstNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixedInstNormedSpace
  Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricDifference2JetNorm_continuous
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    Continuous (fun x : M => metricDifference2JetNorm (I := I) g₀ g₁ g₂ x) := by
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 2
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 3
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 4 I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g₀ 0 4
  let : TopologicalSpace
      (TotalSpace (TensorRSModel 0 2 ℝ E) (fun b : M => TensorRSSpace 0 2 I b)) :=
    pointwiseTensorRSTotalSpaceTopology 0 2
  let : FiberBundle (TensorRSModel 0 2 ℝ E) (fun b : M => TensorRSSpace 0 2 I b) :=
    pointwiseTensorRSFiberBundle 0 2
  let : TopologicalSpace
      (TotalSpace (TensorRSModel 0 3 ℝ E) (fun b : M => TensorRSSpace 0 3 I b)) :=
    pointwiseTensorRSTotalSpaceTopology 0 3
  let : FiberBundle (TensorRSModel 0 3 ℝ E) (fun b : M => TensorRSSpace 0 3 I b) :=
    pointwiseTensorRSFiberBundle 0 3
  let : TopologicalSpace
      (TotalSpace (TensorRSModel 0 4 ℝ E) (fun b : M => TensorRSSpace 0 4 I b)) :=
    pointwiseTensorRSTotalSpaceTopology 0 4
  let : FiberBundle (TensorRSModel 0 4 ℝ E) (fun b : M => TensorRSSpace 0 4 I b) :=
    pointwiseTensorRSFiberBundle 0 4
  have hC2 : IsContinuousRiemannianBundle (TensorRSModel 0 2 ℝ E)
      (fun b : M => TensorRSSpace 0 2 I b) :=
    TensorRSRiemannianBundleContinuous.tensorRS_isContinuousRiemannianBundle
      (I := I) (M := M) g₀ 0 2
  have hC3 : IsContinuousRiemannianBundle (TensorRSModel 0 3 ℝ E)
      (fun b : M => TensorRSSpace 0 3 I b) :=
    TensorRSRiemannianBundleContinuous.tensorRS_isContinuousRiemannianBundle
      (I := I) (M := M) g₀ 0 3
  have hC4 : IsContinuousRiemannianBundle (TensorRSModel 0 4 ℝ E)
      (fun b : M => TensorRSSpace 0 4 I b) :=
    TensorRSRiemannianBundleContinuous.tensorRS_isContinuousRiemannianBundle
      (I := I) (M := M) g₀ 0 4
  have h0 : Continuous (fun x : M => ‖metricDifference02MixedSection (I := I) g₁ g₂ x‖) :=
    continuous_riemannian_fiber_norm_of_continuous_section
      (F₀ := TensorRSModel 0 2 ℝ E) (V₀ := fun b : M => TensorRSSpace 0 2 I b)
      (σ := fun x => metricDifference02MixedSection (I := I) g₁ g₂ x)
      (metricDifference02MixedSection (I := I) g₁ g₂).contMDiff.continuous
  have h1 : Continuous (fun x : M => ‖metricDifference02CovMixedSection (I := I) g₀ g₁ g₂ x‖) :=
    continuous_riemannian_fiber_norm_of_continuous_section
      (F₀ := TensorRSModel 0 3 ℝ E) (V₀ := fun b : M => TensorRSSpace 0 3 I b)
      (σ := fun x => metricDifference02CovMixedSection (I := I) g₀ g₁ g₂ x)
      (metricDifference02CovMixedSection (I := I) g₀ g₁ g₂).contMDiff.continuous
  have h2 : Continuous (fun x : M => ‖metricDifference02CovIterateMixedSection (I := I) g₀ g₁ g₂ x‖) :=
    continuous_riemannian_fiber_norm_of_continuous_section
      (F₀ := TensorRSModel 0 4 ℝ E) (V₀ := fun b : M => TensorRSSpace 0 4 I b)
      (σ := fun x => metricDifference02CovIterateMixedSection (I := I) g₀ g₁ g₂ x)
      (metricDifference02CovIterateMixedSection (I := I) g₀ g₁ g₂).contMDiff.continuous
  have hsum := (h0.add h1).add h2
  refine hsum.congr (fun x => ?_)
  rw [metricDifference2JetNorm_eq_riemannianNorm_sum (I := I) g₀ g₁ g₂ x]
  simp only [Pi.add_apply]

end Spectral
end Analysis
end DifferentialGeometry

end
