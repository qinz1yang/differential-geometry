import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricDifferenceFields
open DifferentialGeometry.Geometry.Curvature
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
open DifferentialGeometry.Analysis.Sobolev.HebeyBlock
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M]

attribute [local instance]
  rhsPointwiseModelDualNormedAddCommGroup
  rhsPointwiseModelDualNormedSpace
  rhsPointwiseModelBilinearNormedAddCommGroup
  rhsPointwiseModelBilinearNormedSpace
  rhsPointwiseModelTrilinearNormedAddCommGroup
  rhsPointwiseModelTrilinearNormedSpace
  rhsPointwiseModelQuadrilinearNormedAddCommGroup
  rhsPointwiseModelQuadrilinearNormedSpace
  rhsPointwiseTangentDualNormedAddCommGroup
  rhsPointwiseTangentDualNormedSpace
  rhsPointwiseTangentBilinearNormedAddCommGroup
  rhsPointwiseTangentBilinearNormedSpace
  rhsPointwiseTangentTrilinearNormedAddCommGroup
  rhsPointwiseTangentTrilinearNormedSpace
  rhsPointwiseTangentTrilinearAddCommGroup
  rhsPointwiseTangentTrilinearModule
  rhsPointwiseTangentTrilinearSMul
  rhsPointwiseTangentTrilinearTopology
  rhsPointwiseSectionAddCommGroup
  rhsPointwiseSectionModule
  rhsPointwiseTangentQuadrilinearNormedAddCommGroup
  rhsPointwiseTangentQuadrilinearNormedSpace
  rhsPointwiseTangentQuadrilinearAddCommGroup
  rhsPointwiseTangentQuadrilinearModule
  rhsPointwiseTangentBilinearAddCommGroup
  rhsPointwiseTangentBilinearModule
  rhsPointwiseBilinearSectionAddCommGroup
  rhsPointwiseBilinearSectionModule
  rhsPointwiseTensor0SModelNormedAddCommGroup
  rhsPointwiseTensor0SModelNormedSpace
  rhsPointwiseTensorRSModelNormedAddCommGroup
  rhsPointwiseTensorRSModelNormedSpace
  rhsPointwiseTensor01TotalSpaceTopology
  rhsPointwiseTensor01FiberBundle
  rhsPointwiseTensor01VectorBundle
  rhsPointwiseTensor01ContMDiffVectorBundle
  rhsPointwiseTensor02TotalSpaceTopology
  rhsPointwiseIteratedTensor02FiberBundle
  rhsPointwiseIteratedTensor02VectorBundle
  rhsPointwiseIteratedTensor02ContMDiffVectorBundle
  rhsPointwiseTensor03TotalSpaceTopology
  rhsPointwiseTensor03FiberBundle
  rhsPointwiseTensor03VectorBundle
  rhsPointwiseTensor03ContMDiffVectorBundle
  rhsPointwiseTensor04TotalSpaceTopology
  rhsPointwiseTensor04FiberBundle
  rhsPointwiseTensor04VectorBundle
  rhsPointwiseTensor04ContMDiffVectorBundle
  rhsPointwiseTensorRSTotalSpaceTopology
  rhsPointwiseTensorRSFiberBundle

private local instance metricDifferenceJetNormTensorRSNormedAddCommGroup
    (r s : ℕ) [Bundle.RiemannianBundle (fun y : M => TensorRSSpace r s I y)] (x : M) :
    NormedAddCommGroup (TensorRSSpace r s I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TensorRSSpace r s I y) x

omit [T2Space M] in
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
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option backward.isDefEq.respectTransparency false in
def metricDiff2JetNorm (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) : ℝ :=
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 4 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
  ‖metricDiff02MixedSection (I := I) g₁ g₂ x‖
    + ‖metricDiff02CovMixedSection (I := I) g₀ g₁ g₂ x‖
    + ‖metricDiff02CovIterateMixedSection (I := I) g₀ g₁ g₂ x‖

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
set_option backward.isDefEq.respectTransparency false in
theorem metricDiff2JetNorm_eq_riemannianNorm_sum [SigmaCompactSpace M]
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 4 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
    metricDiff2JetNorm (I := I) g₀ g₁ g₂ x =
      ‖metricDiff02MixedSection (I := I) g₁ g₂ x‖
        + ‖metricDiff02CovMixedSection (I := I) g₀ g₁ g₂ x‖
        + ‖metricDiff02CovIterateMixedSection (I := I) g₀ g₁ g₂ x‖ :=
  rfl

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
set_option backward.isDefEq.respectTransparency false in
theorem metricDiff2JetNorm_nonneg [SigmaCompactSpace M]
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    0 ≤ metricDiff2JetNorm (I := I) g₀ g₁ g₂ x := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 4 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
  rw [metricDiff2JetNorm_eq_riemannianNorm_sum (I := I) g₀ g₁ g₂ x]
  exact add_nonneg
    (add_nonneg
      (norm_nonneg (metricDiff02MixedSection (I := I) g₁ g₂ x))
      (norm_nonneg (metricDiff02CovMixedSection (I := I) g₀ g₁ g₂ x)))
    (norm_nonneg (metricDiff02CovIterateMixedSection (I := I) g₀ g₁ g₂ x))

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
set_option backward.isDefEq.respectTransparency false in
theorem metricDiff2JetNorm_continuous [SigmaCompactSpace M]
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    Continuous (fun x : M => metricDiff2JetNorm (I := I) g₀ g₁ g₂ x) := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 4 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
  letI : TopologicalSpace
      (TotalSpace (TensorRSModel 0 2 ℝ E) (fun b : M => TensorRSSpace 0 2 I b)) :=
    rhsPointwiseTensorRSTotalSpaceTopology 0 2
  letI : FiberBundle (TensorRSModel 0 2 ℝ E) (fun b : M => TensorRSSpace 0 2 I b) :=
    rhsPointwiseTensorRSFiberBundle 0 2
  letI : TopologicalSpace
      (TotalSpace (TensorRSModel 0 3 ℝ E) (fun b : M => TensorRSSpace 0 3 I b)) :=
    rhsPointwiseTensorRSTotalSpaceTopology 0 3
  letI : FiberBundle (TensorRSModel 0 3 ℝ E) (fun b : M => TensorRSSpace 0 3 I b) :=
    rhsPointwiseTensorRSFiberBundle 0 3
  letI : TopologicalSpace
      (TotalSpace (TensorRSModel 0 4 ℝ E) (fun b : M => TensorRSSpace 0 4 I b)) :=
    rhsPointwiseTensorRSTotalSpaceTopology 0 4
  letI : FiberBundle (TensorRSModel 0 4 ℝ E) (fun b : M => TensorRSSpace 0 4 I b) :=
    rhsPointwiseTensorRSFiberBundle 0 4
  haveI hC2 : IsContinuousRiemannianBundle (TensorRSModel 0 2 ℝ E)
      (fun b : M => TensorRSSpace 0 2 I b) :=
    TensorRSRiemannianBundleContinuous.tensorRS_isContinuousRiemannianBundle
      (I := I) (M := M) g₀ 0 2
  haveI hC3 : IsContinuousRiemannianBundle (TensorRSModel 0 3 ℝ E)
      (fun b : M => TensorRSSpace 0 3 I b) :=
    TensorRSRiemannianBundleContinuous.tensorRS_isContinuousRiemannianBundle
      (I := I) (M := M) g₀ 0 3
  haveI hC4 : IsContinuousRiemannianBundle (TensorRSModel 0 4 ℝ E)
      (fun b : M => TensorRSSpace 0 4 I b) :=
    TensorRSRiemannianBundleContinuous.tensorRS_isContinuousRiemannianBundle
      (I := I) (M := M) g₀ 0 4
  have h0 : Continuous (fun x : M => ‖metricDiff02MixedSection (I := I) g₁ g₂ x‖) :=
    continuous_riemannian_fiber_norm_of_continuous_section
      (F₀ := TensorRSModel 0 2 ℝ E) (V₀ := fun b : M => TensorRSSpace 0 2 I b)
      (σ := fun x => metricDiff02MixedSection (I := I) g₁ g₂ x)
      (metricDiff02MixedSection (I := I) g₁ g₂).contMDiff.continuous
  have h1 : Continuous (fun x : M => ‖metricDiff02CovMixedSection (I := I) g₀ g₁ g₂ x‖) :=
    continuous_riemannian_fiber_norm_of_continuous_section
      (F₀ := TensorRSModel 0 3 ℝ E) (V₀ := fun b : M => TensorRSSpace 0 3 I b)
      (σ := fun x => metricDiff02CovMixedSection (I := I) g₀ g₁ g₂ x)
      (metricDiff02CovMixedSection (I := I) g₀ g₁ g₂).contMDiff.continuous
  have h2 : Continuous (fun x : M => ‖metricDiff02CovIterateMixedSection (I := I) g₀ g₁ g₂ x‖) :=
    continuous_riemannian_fiber_norm_of_continuous_section
      (F₀ := TensorRSModel 0 4 ℝ E) (V₀ := fun b : M => TensorRSSpace 0 4 I b)
      (σ := fun x => metricDiff02CovIterateMixedSection (I := I) g₀ g₁ g₂ x)
      (metricDiff02CovIterateMixedSection (I := I) g₀ g₁ g₂).contMDiff.continuous
  have hsum := (h0.add h1).add h2
  refine hsum.congr (fun x => ?_)
  rw [metricDiff2JetNorm_eq_riemannianNorm_sum (I := I) g₀ g₁ g₂ x]
  simp only [Pi.add_apply]

end Spectral
end Analysis
end DifferentialGeometry

end
