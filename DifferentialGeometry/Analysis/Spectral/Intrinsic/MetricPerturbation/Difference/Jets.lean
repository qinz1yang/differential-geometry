import DifferentialGeometry.Analysis.Spectral.Tensor.PointwiseBundleInstances
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor03CovariantDerivativeCalculus

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

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

def metricDifference02 (g₁ g₂ : SmoothRiemannianMetric I M) :
    Π b : M, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ :=
  fun b => metricTensor02 (I := I) g₁ b - metricTensor02 (I := I) g₂ b

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem metricDifference02_apply
    (g₁ g₂ : SmoothRiemannianMetric I M) (b : M) (v w : TangentSpace I b) :
    metricDifference02 (I := I) g₁ g₂ b v w =
      g₁.inner b v w - g₂.inner b v w := by
  change (metricTensor02 (I := I) g₁ b - metricTensor02 (I := I) g₂ b) v w =
    g₁.inner b v w - g₂.inner b v w
  rw [sub_apply, sub_apply]
  rfl

def metricDifference02Cov (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (b : M) :
    TangentSpace I b →L[ℝ]
      (TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) :=
  (tensor02Cov (LeviCivita (I := I) g₀)).toFun
    (metricDifference02 (I := I) g₁ g₂) b

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem metricDifference02Cov_eq_sub
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (b : M) :
    metricDifference02Cov (I := I) g₀ g₁ g₂ b =
      (tensor02Cov (LeviCivita (I := I) g₀)).toFun
          (metricTensor02 (I := I) g₁) b
        - (tensor02Cov (LeviCivita (I := I) g₀)).toFun
          (metricTensor02 (I := I) g₂) b := by
  classical
  set cov := tensor02Cov (LeviCivita (I := I) g₀) with hcov_def
  have hcovOn := cov.isCovariantDerivativeOnUniv
  have hT₁ : MDiffAtTensor02 (metricTensor02 (I := I) g₁) b :=
    metricTensor02_mdiff (I := I) g₁ b
  have hT₂ : MDiffAtTensor02 (metricTensor02 (I := I) g₂) b :=
    metricTensor02_mdiff (I := I) g₂ b
  have hT₂neg : MDiffAtTensor02 (-(metricTensor02 (I := I) g₂)) b :=
    mdifferentiableAt_neg_section hT₂
  have hneg : cov.toFun (-(metricTensor02 (I := I) g₂)) b =
      - cov.toFun (metricTensor02 (I := I) g₂) b := by
    have hsum : cov.toFun (metricTensor02 (I := I) g₂
          + (-(metricTensor02 (I := I) g₂))) b =
        cov.toFun (metricTensor02 (I := I) g₂) b
          + cov.toFun (-(metricTensor02 (I := I) g₂)) b :=
      hcovOn.add hT₂ hT₂neg (Set.mem_univ b)
    rw [add_neg_cancel] at hsum
    have hzero : cov.toFun (0 : Π x : M,
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b = 0 :=
      hcovOn.zero (Set.mem_univ b)
    rw [hzero] at hsum
    exact eq_neg_of_add_eq_zero_right hsum.symm
  have hadd : cov.toFun (metricTensor02 (I := I) g₁
        + (-(metricTensor02 (I := I) g₂))) b =
      cov.toFun (metricTensor02 (I := I) g₁) b
        + cov.toFun (-(metricTensor02 (I := I) g₂)) b :=
    hcovOn.add hT₁ hT₂neg (Set.mem_univ b)
  have hdiff_eq : metricDifference02 (I := I) g₁ g₂ =
      metricTensor02 (I := I) g₁ + (-(metricTensor02 (I := I) g₂)) := by
    funext c
    simp only [metricDifference02, metricTensor02, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
  calc metricDifference02Cov (I := I) g₀ g₁ g₂ b
      = cov.toFun (metricDifference02 (I := I) g₁ g₂) b := rfl
    _ = cov.toFun (metricTensor02 (I := I) g₁
          + (-(metricTensor02 (I := I) g₂))) b := by rw [hdiff_eq]
    _ = cov.toFun (metricTensor02 (I := I) g₁) b
          + cov.toFun (-(metricTensor02 (I := I) g₂)) b := hadd
    _ = cov.toFun (metricTensor02 (I := I) g₁) b
          - cov.toFun (metricTensor02 (I := I) g₂) b := by rw [hneg]; abel

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricTensor02Cov_mdiffAtTensor03
    (g₀ g : SmoothRiemannianMetric I M) (x : M) :
    MDiffAtTensor03 (I := I)
      ((tensor02Cov (LeviCivita (I := I) g₀)).toFun (metricTensor02 (I := I) g)) x := by
  classical
  have hmetric : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricTensor02 (I := I) g b)) := g.contMDiff
  have hcov : CovariantDerivative.ContMDiffCovariantDerivative
      (tensor02Cov (LeviCivita (I := I) g₀)) ∞ :=
    tensor02Cov_isContMDiff (LeviCivita (I := I) g₀)
  have h_le : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) + 1 := by rw [ENat.coe_top_add_one]
  have hmetric₁ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((∞ : WithTop ℕ∞) + 1)
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricTensor02 (I := I) g b)) Set.univ :=
    contMDiffOn_univ.mpr (hmetric.of_le h_le)
  have hcovOn := hcov.contMDiff
  have hsmooth :=
    hcovOn.contMDiff (σ := metricTensor02 (I := I) g) hmetric₁
  exact (contMDiffOn_univ.mp hsmooth x).mdifferentiableAt (by simp)

def metricDifference02CovIterate (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (b : M) :
    TangentSpace I b →L[ℝ]
      (TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) :=
  tensor02CovIterate (LeviCivita (I := I) g₀) (metricDifference02 (I := I) g₁ g₂) b

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricDifference02CovIterate_eq_sub
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (b : M) :
    metricDifference02CovIterate (I := I) g₀ g₁ g₂ b =
      tensor02CovIterate (LeviCivita (I := I) g₀) (metricTensor02 (I := I) g₁) b
        - tensor02CovIterate (LeviCivita (I := I) g₀) (metricTensor02 (I := I) g₂) b := by
  classical
  set cov := LeviCivita (I := I) g₀ with hcov_def
  have hinner_eq : (tensor02Cov cov).toFun (metricDifference02 (I := I) g₁ g₂) =
      (tensor02Cov cov).toFun (metricTensor02 (I := I) g₁)
        - (tensor02Cov cov).toFun (metricTensor02 (I := I) g₂) := by
    funext c
    have h := metricDifference02Cov_eq_sub (I := I) g₀ g₁ g₂ c
    have hlhs : metricDifference02Cov (I := I) g₀ g₁ g₂ c =
        (tensor02Cov cov).toFun (metricDifference02 (I := I) g₁ g₂) c := rfl
    rw [hlhs] at h
    rw [h]
    rfl
  have hS₁ : MDiffAtTensor03 (I := I)
      ((tensor02Cov cov).toFun (metricTensor02 (I := I) g₁)) b :=
    metricTensor02Cov_mdiffAtTensor03 (I := I) g₀ g₁ b
  have hS₂ : MDiffAtTensor03 (I := I)
      ((tensor02Cov cov).toFun (metricTensor02 (I := I) g₂)) b :=
    metricTensor02Cov_mdiffAtTensor03 (I := I) g₀ g₂ b
  calc metricDifference02CovIterate (I := I) g₀ g₁ g₂ b
      = (tensor03Cov cov).toFun
          ((tensor02Cov cov).toFun (metricDifference02 (I := I) g₁ g₂)) b := rfl
    _ = (tensor03Cov cov).toFun
          ((tensor02Cov cov).toFun (metricTensor02 (I := I) g₁)
            - (tensor02Cov cov).toFun (metricTensor02 (I := I) g₂)) b := by
        rw [hinner_eq]
    _ = (tensor03Cov cov).toFun
          ((tensor02Cov cov).toFun (metricTensor02 (I := I) g₁)) b
        - (tensor03Cov cov).toFun
          ((tensor02Cov cov).toFun (metricTensor02 (I := I) g₂)) b :=
        tensor03Cov_sub cov hS₁ hS₂
    _ = tensor02CovIterate cov (metricTensor02 (I := I) g₁) b
        - tensor02CovIterate cov (metricTensor02 (I := I) g₂) b := rfl

end Spectral
end Analysis
end DifferentialGeometry

end
