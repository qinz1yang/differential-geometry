import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSPointwiseBundleModels
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

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

def metricDiff02 (g₁ g₂ : SmoothRiemannianMetric I M) :
    Π b : M, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ :=
  fun b => metricTensor02 (I := I) g₁ b - metricTensor02 (I := I) g₂ b

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] in
@[simp] theorem metricDiff02_apply
    (g₁ g₂ : SmoothRiemannianMetric I M) (b : M) (v w : TangentSpace I b) :
    metricDiff02 (I := I) g₁ g₂ b v w =
      g₁.inner b v w - g₂.inner b v w := by
  change (metricTensor02 (I := I) g₁ b - metricTensor02 (I := I) g₂ b) v w =
    g₁.inner b v w - g₂.inner b v w
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
  rfl






def metricDiff02Cov (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (b : M) :
    TangentSpace I b →L[ℝ]
      (TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) :=
  (tensor02Cov (LeviCivita (I := I) g₀)).toFun
    (metricDiff02 (I := I) g₁ g₂) b





omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [T2Space M] in
theorem metricDiff02Cov_eq_sub
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (b : M) :
    metricDiff02Cov (I := I) g₀ g₁ g₂ b =
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
  have hdiff_eq : metricDiff02 (I := I) g₁ g₂ =
      metricTensor02 (I := I) g₁ + (-(metricTensor02 (I := I) g₂)) := by
    funext c
    simp only [metricDiff02, metricTensor02, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
  calc metricDiff02Cov (I := I) g₀ g₁ g₂ b
      = cov.toFun (metricDiff02 (I := I) g₁ g₂) b := rfl
    _ = cov.toFun (metricTensor02 (I := I) g₁
          + (-(metricTensor02 (I := I) g₂))) b := by rw [hdiff_eq]
    _ = cov.toFun (metricTensor02 (I := I) g₁) b
          + cov.toFun (-(metricTensor02 (I := I) g₂)) b := hadd
    _ = cov.toFun (metricTensor02 (I := I) g₁) b
          - cov.toFun (metricTensor02 (I := I) g₂) b := by rw [hneg]; abel






omit [NeZero (Module.finrank ℝ E)] in
theorem metricTensor02Cov_mdiffAtTensor03
    (g₀ g : SmoothRiemannianMetric I M) (x : M) :
    MDiffAtTensor03 (I := I)
      ((tensor02Cov (LeviCivita (I := I) g₀)).toFun (metricTensor02 (I := I) g)) x := by
  classical
  have hmetric : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricTensor02 (I := I) g b)) := g.contMDiff
  haveI hcov : CovariantDerivative.ContMDiffCovariantDerivative
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






def metricDiff02CovIterate (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (b : M) :
    TangentSpace I b →L[ℝ]
      (TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) :=
  tensor02CovIterate (LeviCivita (I := I) g₀) (metricDiff02 (I := I) g₁ g₂) b








omit [NeZero (Module.finrank ℝ E)] in
theorem metricDiff02CovIterate_eq_sub
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (b : M) :
    metricDiff02CovIterate (I := I) g₀ g₁ g₂ b =
      tensor02CovIterate (LeviCivita (I := I) g₀) (metricTensor02 (I := I) g₁) b
        - tensor02CovIterate (LeviCivita (I := I) g₀) (metricTensor02 (I := I) g₂) b := by
  classical
  set cov := LeviCivita (I := I) g₀ with hcov_def
  have hinner_eq : (tensor02Cov cov).toFun (metricDiff02 (I := I) g₁ g₂) =
      (tensor02Cov cov).toFun (metricTensor02 (I := I) g₁)
        - (tensor02Cov cov).toFun (metricTensor02 (I := I) g₂) := by
    funext c
    have h := metricDiff02Cov_eq_sub (I := I) g₀ g₁ g₂ c
    have hlhs : metricDiff02Cov (I := I) g₀ g₁ g₂ c =
        (tensor02Cov cov).toFun (metricDiff02 (I := I) g₁ g₂) c := rfl
    rw [hlhs] at h
    rw [h]
    rfl
  have hS₁ : MDiffAtTensor03 (I := I)
      ((tensor02Cov cov).toFun (metricTensor02 (I := I) g₁)) b :=
    metricTensor02Cov_mdiffAtTensor03 (I := I) g₀ g₁ b
  have hS₂ : MDiffAtTensor03 (I := I)
      ((tensor02Cov cov).toFun (metricTensor02 (I := I) g₂)) b :=
    metricTensor02Cov_mdiffAtTensor03 (I := I) g₀ g₂ b
  calc metricDiff02CovIterate (I := I) g₀ g₁ g₂ b
      = (tensor03Cov cov).toFun
          ((tensor02Cov cov).toFun (metricDiff02 (I := I) g₁ g₂)) b := rfl
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
