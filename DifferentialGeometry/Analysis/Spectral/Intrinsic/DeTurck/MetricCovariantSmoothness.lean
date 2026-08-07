import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricDifferenceJets
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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] in
theorem tensor03_pairing_contMDiff
    {S : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b)))
    {Y Z W : Π x : M, TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (Y b)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (Z b)))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (W b))) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => S b (Y b) (Z b) (W b)) := by
  have h1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b (Y b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
      (b := fun b : M => b) (ϕ := fun b => S b) (v := fun b => Y b) hS hY
  have h2 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) b (S b (Y b) (Z b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
      (b := fun b : M => b) (ϕ := fun b => S b (Y b)) (v := fun b => Z b) h1 hZ
  have h3 : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : M => TotalSpace.mk' ℝ (E := fun _ : M => ℝ) b (S b (Y b) (Z b) (W b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun _ : M => ℝ)
      (b := fun b : M => b) (ϕ := fun b => S b (Y b) (Z b)) (v := fun b => W b) h2 hW
  intro x
  exact (contMDiffAt_section (F := ℝ) (E := fun _ : M => ℝ) x).mp (h3 x)






omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    in
private theorem tensor03Cov_quad_apply_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {S : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b)))
    (Y Z W U : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => ((((tensor03Cov cov).toFun S x (Y x)) (Z x)) (W x)) (U x)) := by
  have h_eq : ∀ x : M,
      ((((tensor03Cov cov).toFun S x (Y x)) (Z x)) (W x)) (U x) =
        extDerivFun (I := I) (fun b => S b (Z b) (W b) (U b)) x (Y x)
          - S x (cov.toFun Z x (Y x)) (W x) (U x)
          - S x (Z x) (cov.toFun W x (Y x)) (U x)
          - S x (Z x) (W x) (cov.toFun U x (Y x)) := by
    intro x
    have hSx : MDiffAtTensor03 S x := (hS x).mdifferentiableAt (by simp)
    have hYx := (Y.contMDiff x).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have hZx := (Z.contMDiff x).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have hWx := (W.contMDiff x).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have hUx := (U.contMDiff x).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have h := tensor03CovAt_apply_of_diff_extend cov hSx hYx hZx hWx hUx
    rw [tensor03Cov_toFun, tensor03CovFun_apply, h]
    rfl
  have h_pair : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => S b (Z b) (W b) (U b)) :=
    tensor03_pairing_contMDiff hS Z.contMDiff W.contMDiff U.contMDiff
  have h_extDeriv : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x)
        x (extDerivFun (I := I) (fun b => S b (Z b) (W b) (U b)) x)) :=
    cotangentCov_extDerivFun_smooth h_pair
  have h_extDeriv_Y : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => extDerivFun (I := I) (fun b => S b (Z b) (W b) (U b)) x (Y x)) := by
    have hap : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun x => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) x
          (extDerivFun (I := I) (fun b => S b (Z b) (W b) (U b)) x (Y x))) :=
      ContMDiff.clm_bundle_apply
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => (Bundle.Trivial M ℝ) x)
        (b := fun x : M => x)
        (ϕ := fun x => extDerivFun (I := I) (fun b => S b (Z b) (W b) (U b)) x)
        (v := fun x => Y x) h_extDeriv Y.contMDiff
    intro x
    exact (contMDiffAt_section (F := ℝ) (E := Bundle.Trivial M ℝ) x).mp (hap x)
  have h_covApp : ∀ (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x => TotalSpace.mk' E (E := TangentSpace I) x (cov.toFun (fun y => V y) x (Y x))) := by
    intro V
    have hcovV : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun x => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) x
          (cov.toFun (fun y => V y) x)) :=
      cotangentCov_covApply_smooth cov V.contMDiff
    exact ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x)
      (b := fun x : M => x) (ϕ := fun x => cov.toFun (fun y => V y) x)
      (v := fun x => Y x) hcovV Y.contMDiff
  have h_t1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => S x (cov.toFun Z x (Y x)) (W x) (U x)) :=
    tensor03_pairing_contMDiff hS (h_covApp Z) W.contMDiff U.contMDiff
  have h_t2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => S x (Z x) (cov.toFun W x (Y x)) (U x)) :=
    tensor03_pairing_contMDiff hS Z.contMDiff (h_covApp W) U.contMDiff
  have h_t3 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => S x (Z x) (W x) (cov.toFun U x (Y x))) :=
    tensor03_pairing_contMDiff hS Z.contMDiff W.contMDiff (h_covApp U)
  have h_combined : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => extDerivFun (I := I) (fun b => S b (Z b) (W b) (U b)) x (Y x)
        - S x (cov.toFun Z x (Y x)) (W x) (U x)
        - S x (Z x) (cov.toFun W x (Y x)) (U x)
        - S x (Z x) (W x) (cov.toFun U x (Y x))) :=
    ((h_extDeriv_Y.sub h_t1).sub h_t2).sub h_t3
  exact h_combined.congr (fun x => h_eq x)







omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem tensor03Cov_output_apply3_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {S : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b)))
    (Y Z W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) x
        ((tensor03Cov cov).toFun S x (Y x) (Z x) (W x))) := by
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x => (tensor03Cov cov).toFun S x (Y x) (Z x) (W x))
  intro U
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => ((((tensor03Cov cov).toFun S x (Y x)) (Z x)) (W x)) (U x)) :=
    tensor03Cov_quad_apply_smooth cov hS Y Z W U
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change ((((tensor03Cov cov).toFun S y (Y y)) (Z y)) (W y)) (U y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x
      ⟨y, ((((tensor03Cov cov).toFun S y (Y y)) (Z y)) (W y)) (U y)⟩).2
  rfl



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem tensor03Cov_output_apply2_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {S : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b)))
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        ((tensor03Cov cov).toFun S x (Y x) (Z x))) := by
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x => (tensor03Cov cov).toFun S x (Y x) (Z x))
  intro W
  exact tensor03Cov_output_apply3_contMDiff cov hS Y Z W



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem tensor03Cov_output_apply_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {S : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b)))
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        ((tensor03Cov cov).toFun S x (Y x))) := by
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ))
    (φ := fun x => (tensor03Cov cov).toFun S x (Y x))
  intro Z
  exact tensor03Cov_output_apply2_contMDiff cov hS Y Z



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem tensor03Cov_output_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {S : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))) ∞
      (fun x : M => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))
        (E := fun x : M => TangentSpace I x →L[ℝ]
          (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))) x
        ((tensor03Cov cov).toFun S x)) := by
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ]
      (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))
    (φ := fun x => (tensor03Cov cov).toFun S x)
  intro Y
  exact tensor03Cov_output_apply_contMDiff cov hS Y





omit [NeZero (Module.finrank ℝ E)] in
theorem tensor02CovIterate_metric_contMDiff
    (g₀ g : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))) ∞
      (fun x : M => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))
        (E := fun x : M => TangentSpace I x →L[ℝ]
          (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))) x
        (tensor02CovIterate (LeviCivita (I := I) g₀) (metricTensor02 (I := I) g) x)) := by
  haveI hcov : CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita (I := I) g₀) ∞ := inferInstance
  have h_metric : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricTensor02 (I := I) g b)) := g.contMDiff
  have h_le : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) + 1 := by rw [ENat.coe_top_add_one]
  have h_metric₁ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((∞ : WithTop ℕ∞) + 1)
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricTensor02 (I := I) g b)) Set.univ :=
    contMDiffOn_univ.mpr (h_metric.of_le h_le)
  have hS₃ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        ((tensor02Cov (LeviCivita (I := I) g₀)).toFun (metricTensor02 (I := I) g) x)) :=
    contMDiffOn_univ.mp
      ((tensor02Cov_isContMDiff (LeviCivita (I := I) g₀)).contMDiff.contMDiff
        (σ := metricTensor02 (I := I) g) h_metric₁)
  exact tensor03Cov_output_contMDiff (LeviCivita (I := I) g₀) hS₃





omit [NeZero (Module.finrank ℝ E)] in
theorem tensor02Cov_metric_contMDiff
    (g₀ g : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        ((tensor02Cov (LeviCivita (I := I) g₀)).toFun (metricTensor02 (I := I) g) x)) := by
  have h_metric : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricTensor02 (I := I) g b)) := g.contMDiff
  have h_le : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) + 1 := by rw [ENat.coe_top_add_one]
  have h_metric₁ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((∞ : WithTop ℕ∞) + 1)
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricTensor02 (I := I) g b)) Set.univ :=
    contMDiffOn_univ.mpr (h_metric.of_le h_le)
  exact contMDiffOn_univ.mp
    ((tensor02Cov_isContMDiff (LeviCivita (I := I) g₀)).contMDiff.contMDiff
      (σ := metricTensor02 (I := I) g) h_metric₁)







end Spectral
end Analysis
end DifferentialGeometry

end
