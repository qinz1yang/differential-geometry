import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricPerturbation.Difference.CovariantSmoothness
import DifferentialGeometry.Geometry.Coordinates.Frame.Chart
import DifferentialGeometry.Tensor.Mixed.Field

open DifferentialGeometry.Tensor.Multilinear
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
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [hIBoundaryless : I.Boundaryless] [hT2Space : T2Space M]
  [SigmaCompactSpace M]

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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
private theorem tensor02_pairing_contMDiff
    {S : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b)))
    {Y Z : Π x : M, TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (Y b)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (Z b))) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => S b (Y b) (Z b)) := by
  have h1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) b (S b (Y b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
      (b := fun b : M => b) (ϕ := fun b => S b) (v := fun b => Y b) hS hY
  have h2 : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : M => TotalSpace.mk' ℝ (E := fun _ : M => ℝ) b (S b (Y b) (Z b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun _ : M => ℝ)
      (b := fun b : M => b) (ϕ := fun b => S b (Y b)) (v := fun b => Z b) h1 hZ
  intro x
  exact (contMDiffAt_section (F := ℝ) (E := fun _ : M => ℝ) x).mp (h2 x)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
private theorem tensor04_pairing_contMDiff
    {S : Π x : M, TangentSpace I x →L[ℝ]
      (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))
        (E := fun x : M => TangentSpace I x →L[ℝ]
          (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))) b (S b)))
    {Y Z W U : Π x : M, TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (Y b)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (Z b)))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (W b)))
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (U b))) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => S b (Y b) (Z b) (W b) (U b)) := by
  have h1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b (Y b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M =>
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
      (b := fun b : M => b) (ϕ := fun b => S b) (v := fun b => Y b) hS hY
  exact tensor03_pairing_contMDiff h1 hZ hW hU

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem chartFrame_component_contMDiffOn
    {S : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b)))
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => S x (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x))
      (chartAt H α).source := by
  classical
  intro x₀ hx₀
  have h_frame_on : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b))
        (chartAt H α).source := fun k => DifferentialGeometry.Tensor.Coordinates.chartAlphaFrame_section_contMDiffOn (I := I) α k
  obtain ⟨Sf, hSf_eq⟩ :=
    exists_contMDiffSection_eqOn_nhd
      (s := fun k : Fin (Module.finrank ℝ E) => fun b : M => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b)
      (u := (chartAt H α).source) (p := x₀)
      h_frame_on ((chartAt H α).open_source) hx₀
  have hSf_smooth : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E b ((Sf k) b : TangentSpace I b)) :=
    fun k => (Sf k).contMDiff
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => S b ((Sf i) b) ((Sf j) b)) :=
    tensor02_pairing_contMDiff hS (hSf_smooth i) (hSf_smooth j)
  have h_chart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => S x (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x)) x₀ := by
    refine (h_scalar x₀).congr_of_eventuallyEq ?_
    filter_upwards [hSf_eq] with b hb
    rw [hb i, hb j]
  exact h_chart_at.contMDiffWithinAt

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
private theorem metricDifference02_contMDiff (g₁ g₂ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricDifference02 (I := I) g₁ g₂ b)) := by
  have hsub :
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricDifference02 (I := I) g₁ g₂ b)) =
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (g₁.inner b - g₂.inner b)) := by
    funext c; rfl
  rw [hsub]
  exact g₁.contMDiff.sub_section g₂.contMDiff

private def metricDifference02ModelFun (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x :=
  Tensor0SSpace.ofModel (I := I)
    (biForm₂ToModel (TangentSpace I x) (metricDifference02 (I := I) g₁ g₂ x))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
private theorem metricDifference02ModelFun_toModel_apply
    (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel (metricDifference02ModelFun (I := I) g₁ g₂ x) v =
      metricDifference02 (I := I) g₁ g₂ x (v 0) (v 1) := by
  unfold metricDifference02ModelFun
  change (biForm₂ToModel (TangentSpace I x)
    (metricDifference02 (I := I) g₁ g₂ x)) v = _
  exact biForm₂ToModel_apply (TangentSpace I x) (metricDifference02 (I := I) g₁ g₂ x) v

def metricDifference02Field (g₁ g₂ : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  letI := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => metricDifference02ModelFun (I := I) g₁ g₂ x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord
      (𝕜 := ℝ) (F := E) (E := (TangentSpace I : M → Type _)) (IB := I)
      (n := (∞ : WithTop ℕ∞)) b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M => metricDifference02 (I := I) g₁ g₂ x
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (σ 0) x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (σ 1) x))
        (chartAt H x₀).source :=
      chartFrame_component_contMDiffOn (I := I)
        (metricDifference02_contMDiff (I := I) g₁ g₂) x₀ (σ 0) (σ 1)
    have hx₀_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have h_src_nhd : (chartAt H x₀).source ∈ 𝓝 x₀ :=
      (chartAt H x₀).open_source.mem_nhds hx₀_src
    refine ((hcomp x₀ hx₀_src).contMDiffAt h_src_nhd).congr_of_eventuallyEq ?_
    have h_base_nhd :
        (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ :=
      (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀_base
    filter_upwards [h_base_nhd] with x hx
    rw [continuousMultilinearMap_basis_repr]
    change Tensor0SSpace.toModel (metricDifference02ModelFun (I := I) g₁ g₂ x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [metricDifference02ModelFun_toModel_apply]
    rfl⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
include hT2Space in
@[simp] theorem metricDifference02Field_toModel_apply
    (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) (v : Fin 2 → TangentSpace I x) :
    metricDifference02Field (I := I) g₁ g₂ x v =
      metricDifference02 (I := I) g₁ g₂ x (v 0) (v 1) :=
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem metricDifference02Cov_contMDiff (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        (metricDifference02Cov (I := I) g₀ g₁ g₂ x)) := by
  have hsub :
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        (metricDifference02Cov (I := I) g₀ g₁ g₂ x)) =
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        ((tensor02Cov (LeviCivita (I := I) g₀)).toFun (metricTensor02 (I := I) g₁) x
          - (tensor02Cov (LeviCivita (I := I) g₀)).toFun (metricTensor02 (I := I) g₂) x)) := by
    funext c
    exact congrArg _ (metricDifference02Cov_eq_sub (I := I) g₀ g₁ g₂ c)
  rw [hsub]
  exact (tensor02Cov_metric_contMDiff (I := I) g₀ g₁).sub_section
    (tensor02Cov_metric_contMDiff (I := I) g₀ g₂)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem chartFrame_component3_contMDiffOn
    {S : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b)))
    (α : M) (i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => S x (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x))
      (chartAt H α).source := by
  classical
  intro x₁ hx₁
  have h_frame_on : ∀ m : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun c : M => TotalSpace.mk' E c (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m c))
        (chartAt H α).source := fun m => DifferentialGeometry.Tensor.Coordinates.chartAlphaFrame_section_contMDiffOn (I := I) α m
  obtain ⟨Sf, hSf_eq⟩ :=
    exists_contMDiffSection_eqOn_nhd
      (s := fun m : Fin (Module.finrank ℝ E) => fun c : M => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m c)
      (u := (chartAt H α).source) (p := x₁)
      h_frame_on ((chartAt H α).open_source) hx₁
  have hSf_smooth : ∀ m : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun c : M => TotalSpace.mk' E c ((Sf m) c : TangentSpace I c)) :=
    fun m => (Sf m).contMDiff
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun c : M => S c ((Sf i) c) ((Sf j) c) ((Sf k) c)) :=
    tensor03_pairing_contMDiff hS (hSf_smooth i) (hSf_smooth j) (hSf_smooth k)
  have h_chart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => S x (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x)) x₁ := by
    refine (h_scalar x₁).congr_of_eventuallyEq ?_
    filter_upwards [hSf_eq] with c hc
    rw [hc i, hc j, hc k]
  exact h_chart_at.contMDiffWithinAt

private def metricDifference02CovModelFun (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 3 I x :=
  Tensor0SSpace.ofModel (I := I)
    (triFormToModel (TangentSpace I x) (metricDifference02Cov (I := I) g₀ g₁ g₂ x))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [T2Space M] [SigmaCompactSpace M] in
private theorem metricDifference02CovModelFun_toModel_apply
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) (v : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel (metricDifference02CovModelFun (I := I) g₀ g₁ g₂ x) v =
      metricDifference02Cov (I := I) g₀ g₁ g₂ x (v 0) (v 1) (v 2) := by
  unfold metricDifference02CovModelFun
  change (triFormToModel (TangentSpace I x)
    (metricDifference02Cov (I := I) g₀ g₁ g₂ x)) v = _
  exact triFormToModel_apply (TangentSpace I x) (metricDifference02Cov (I := I) g₀ g₁ g₂ x) v

def metricDifference02CovField (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => metricDifference02CovModelFun (I := I) g₀ g₁ g₂ x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord
      (𝕜 := ℝ) (F := E) (E := (TangentSpace I : M → Type _)) (IB := I)
      (n := (∞ : WithTop ℕ∞)) b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M => metricDifference02Cov (I := I) g₀ g₁ g₂ x
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (σ 0) x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (σ 1) x)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (σ 2) x))
        (chartAt H x₀).source :=
      chartFrame_component3_contMDiffOn (I := I)
        (metricDifference02Cov_contMDiff (I := I) g₀ g₁ g₂) x₀ (σ 0) (σ 1) (σ 2)
    have hx₀_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have h_src_nhd : (chartAt H x₀).source ∈ 𝓝 x₀ :=
      (chartAt H x₀).open_source.mem_nhds hx₀_src
    refine ((hcomp x₀ hx₀_src).contMDiffAt h_src_nhd).congr_of_eventuallyEq ?_
    have h_base_nhd :
        (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ :=
      (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀_base
    filter_upwards [h_base_nhd] with x hx
    rw [continuousMultilinearMap_basis_repr]
    change Tensor0SSpace.toModel (metricDifference02CovModelFun (I := I) g₀ g₁ g₂ x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [metricDifference02CovModelFun_toModel_apply]
    rfl⟩

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
include hIBoundaryless hT2Space in
@[simp] theorem metricDifference02CovField_toModel_apply
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) (v : Fin 3 → TangentSpace I x) :
    metricDifference02CovField (I := I) g₀ g₁ g₂ x v =
      metricDifference02Cov (I := I) g₀ g₁ g₂ x (v 0) (v 1) (v 2) :=
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem metricDifference02CovIterate_contMDiff (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))
        (E := fun x : M => TangentSpace I x →L[ℝ]
          (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))) x
        (metricDifference02CovIterate (I := I) g₀ g₁ g₂ x)) := by
  have hS₁ := tensor02CovIterate_metric_contMDiff (I := I) g₀ g₁
  have hS₂ := tensor02CovIterate_metric_contMDiff (I := I) g₀ g₂
  have hsub :
      (fun x : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))
        (E := fun x : M => TangentSpace I x →L[ℝ]
          (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))) x
        (metricDifference02CovIterate (I := I) g₀ g₁ g₂ x)) =
      (fun x : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))
        (E := fun x : M => TangentSpace I x →L[ℝ]
          (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))) x
        (tensor02CovIterate (LeviCivita (I := I) g₀) (metricTensor02 (I := I) g₁) x
          - tensor02CovIterate (LeviCivita (I := I) g₀) (metricTensor02 (I := I) g₂) x)) := by
    funext c
    exact congrArg _ (metricDifference02CovIterate_eq_sub (I := I) g₀ g₁ g₂ c)
  rw [hsub]
  exact hS₁.sub_section hS₂

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem chartFrame_component4_contMDiffOn
    {S : Π x : M, TangentSpace I x →L[ℝ]
      (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))
        (E := fun x : M => TangentSpace I x →L[ℝ]
          (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))) b (S b)))
    (α : M) (i j k l : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => S x (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α l x))
      (chartAt H α).source := by
  classical
  intro x₁ hx₁
  have h_frame_on : ∀ m : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun c : M => TotalSpace.mk' E c (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m c))
        (chartAt H α).source := fun m => DifferentialGeometry.Tensor.Coordinates.chartAlphaFrame_section_contMDiffOn (I := I) α m
  obtain ⟨Sf, hSf_eq⟩ :=
    exists_contMDiffSection_eqOn_nhd
      (s := fun m : Fin (Module.finrank ℝ E) => fun c : M => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m c)
      (u := (chartAt H α).source) (p := x₁)
      h_frame_on ((chartAt H α).open_source) hx₁
  have hSf_smooth : ∀ m : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun c : M => TotalSpace.mk' E c ((Sf m) c : TangentSpace I c)) :=
    fun m => (Sf m).contMDiff
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun c : M => S c ((Sf i) c) ((Sf j) c) ((Sf k) c) ((Sf l) c)) :=
    tensor04_pairing_contMDiff hS (hSf_smooth i) (hSf_smooth j) (hSf_smooth k) (hSf_smooth l)
  have h_chart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => S x (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α l x)) x₁ := by
    refine (h_scalar x₁).congr_of_eventuallyEq ?_
    filter_upwards [hSf_eq] with c hc
    rw [hc i, hc j, hc k, hc l]
  exact h_chart_at.contMDiffWithinAt

private def metricDifference02CovIterateModelFun (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 4 I x :=
  Tensor0SSpace.ofModel (I := I)
    (quadFormToModel (TangentSpace I x) (metricDifference02CovIterate (I := I) g₀ g₁ g₂ x))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [T2Space M] [SigmaCompactSpace M] in
private theorem metricDifference02CovIterateModelFun_toModel_apply
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) (v : Fin 4 → TangentSpace I x) :
    Tensor0SSpace.toModel (metricDifference02CovIterateModelFun (I := I) g₀ g₁ g₂ x) v =
      metricDifference02CovIterate (I := I) g₀ g₁ g₂ x (v 0) (v 1) (v 2) (v 3) := by
  unfold metricDifference02CovIterateModelFun
  change (quadFormToModel (TangentSpace I x)
    (metricDifference02CovIterate (I := I) g₀ g₁ g₂ x)) v = _
  exact quadFormToModel_apply (TangentSpace I x) (metricDifference02CovIterate (I := I) g₀ g₁ g₂ x) v

def metricDifference02CovIterateField (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 4 :=
  letI := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => metricDifference02CovIterateModelFun (I := I) g₀ g₁ g₂ x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord
      (𝕜 := ℝ) (F := E) (E := (TangentSpace I : M → Type _)) (IB := I)
      (n := (∞ : WithTop ℕ∞)) b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M => metricDifference02CovIterate (I := I) g₀ g₁ g₂ x
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (σ 0) x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (σ 1) x)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (σ 2) x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (σ 3) x))
        (chartAt H x₀).source :=
      chartFrame_component4_contMDiffOn (I := I)
        (metricDifference02CovIterate_contMDiff (I := I) g₀ g₁ g₂) x₀ (σ 0) (σ 1) (σ 2) (σ 3)
    have hx₀_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have h_src_nhd : (chartAt H x₀).source ∈ 𝓝 x₀ :=
      (chartAt H x₀).open_source.mem_nhds hx₀_src
    refine ((hcomp x₀ hx₀_src).contMDiffAt h_src_nhd).congr_of_eventuallyEq ?_
    have h_base_nhd :
        (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ :=
      (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀_base
    filter_upwards [h_base_nhd] with x hx
    rw [continuousMultilinearMap_basis_repr]
    change Tensor0SSpace.toModel (metricDifference02CovIterateModelFun (I := I) g₀ g₁ g₂ x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [metricDifference02CovIterateModelFun_toModel_apply]
    rfl⟩

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
include hIBoundaryless hT2Space in
@[simp] theorem metricDifference02CovIterateField_toModel_apply
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) (v : Fin 4 → TangentSpace I x) :
    metricDifference02CovIterateField (I := I) g₀ g₁ g₂ x v =
      metricDifference02CovIterate (I := I) g₀ g₁ g₂ x (v 0) (v 1) (v 2) (v 3) :=
  rfl

def metricDifference02MixedSection (g₁ g₂ : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (metricDifference02Field (I := I) g₁ g₂)

def metricDifference02CovMixedSection (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 3 ℝ E, (fun x : M => TensorRSSpace 0 3 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (metricDifference02CovField (I := I) g₀ g₁ g₂)

def metricDifference02CovIterateMixedSection (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 4 ℝ E, (fun x : M => TensorRSSpace 0 4 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (metricDifference02CovIterateField (I := I) g₀ g₁ g₂)

end Spectral
end Analysis
end DifferentialGeometry

end
