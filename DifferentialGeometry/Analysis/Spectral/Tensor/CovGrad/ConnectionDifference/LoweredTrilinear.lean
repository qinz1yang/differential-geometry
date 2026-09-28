import DifferentialGeometry.Tensor.RSTensor.Reindexing.Permutation
import DifferentialGeometry.Tensor.RSTensor.Algebra.Product
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.OperatorField.Application
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.CorrectionFields.ChristoffelCoefficients
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Parametric.JointSmoothness
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.ContractedBianchi
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.SlotSubstitutionBound
open DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private noncomputable def trilinFormToModel (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F] (B : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => F) ℝ := by
  letI : NormedAddCommGroup (F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => F) ℝ).symm
    (((ContinuousLinearEquiv.refl ℝ F).arrowCongr
      (biForm₂ToModelₗᵢ F).toContinuousLinearEquiv) B)

private theorem trilinFormToModel_apply (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) (v : Fin 3 → F) :
    trilinFormToModel F B v = B (v 0) (v 1) (v 2) := by
  classical
  let : NormedAddCommGroup (F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => F) ℝ).symm
      (((ContinuousLinearEquiv.refl ℝ F).arrowCongr
          (biForm₂ToModelₗᵢ F).toContinuousLinearEquiv) B) v =
    B (v 0) (v 1) (v 2)
  rw [continuousMultilinearCurryLeftEquiv_symm_apply,
    ContinuousLinearEquiv.arrowCongr_apply]
  simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [show ((biForm₂ToModelₗᵢ F) (B (v 0)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => F) ℝ)
      = biForm₂ToModel F (B (v 0)) from rfl]
  rw [biForm₂ToModel_apply]
  rfl

noncomputable def metricConnectionDifferenceLoweredTrilin (gm gA gB : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x)
      (TangentSpace I x →L[ℝ] ℝ) (gm.inner x)).comp
    (PDE.DeTurck.connectionDifference (I := I) gA gB x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem metricConnectionDifferenceLoweredTrilin_apply (gm gA gB : SmoothRiemannianMetric I M) (x : M)
    (a b c : TangentSpace I x) :
    metricConnectionDifferenceLoweredTrilin (I := I) gm gA gB x a b c =
      gm.inner x (PDE.DeTurck.connectionDifference (I := I) gA gB x a b) c := by
  rw [metricConnectionDifferenceLoweredTrilin]
  rfl

noncomputable def metricConnectionDifferenceLoweredFib (gm gA gB : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x :=
  (Tensor0SBundle.tensor0SSpaceFiberContinuousLinearEquiv
    (I := I) 3 x).symm
    (trilinFormToModel (TangentSpace I x) (metricConnectionDifferenceLoweredTrilin (I := I) gm gA gB x))

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem metricConnectionDifferenceLoweredFib_toModel (gm gA gB : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 3 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (metricConnectionDifferenceLoweredFib (I := I) gm gA gB x) v =
      gm.inner x (PDE.DeTurck.connectionDifference (I := I) gA gB x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2)) := by
  rw [metricConnectionDifferenceLoweredFib,
    Tensor0SBundle.Tensor0SSpace.toModel_apply_model_vector]
  change (trilinFormToModel (TangentSpace I x))
      (metricConnectionDifferenceLoweredTrilin (I := I) gm gA gB x)
        (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i)) = _
  rw [trilinFormToModel_apply, metricConnectionDifferenceLoweredTrilin_apply]

noncomputable def ccBilinConnectionDifferenceLoweredTrilin (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x)
      (TangentSpace I x →L[ℝ] ℝ) (ccTensorBilinSymm (I := I) g₀ V x)).comp
    (PDE.DeTurck.connectionDifference (I := I) gA gB x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem ccBilinConnectionDifferenceLoweredTrilin_apply (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M)
    (a b c : TangentSpace I x) :
    ccBilinConnectionDifferenceLoweredTrilin (I := I) g₀ V gA gB x a b c =
      ccTensorBilinSymm (I := I) g₀ V x (PDE.DeTurck.connectionDifference (I := I) gA gB x a b) c := by
  rw [ccBilinConnectionDifferenceLoweredTrilin]
  rfl

noncomputable def ccBilinConnectionDifferenceLoweredFib (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x :=
  (Tensor0SBundle.tensor0SSpaceFiberContinuousLinearEquiv
    (I := I) 3 x).symm
    (trilinFormToModel (TangentSpace I x) (ccBilinConnectionDifferenceLoweredTrilin (I := I) g₀ V gA gB x))

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem ccBilinConnectionDifferenceLoweredFib_toModel (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 3 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (ccBilinConnectionDifferenceLoweredFib (I := I) g₀ V gA gB x) v =
      ccTensorBilinSymm (I := I) g₀ V x
        (PDE.DeTurck.connectionDifference (I := I) gA gB x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2)) := by
  rw [ccBilinConnectionDifferenceLoweredFib,
    Tensor0SBundle.Tensor0SSpace.toModel_apply_model_vector]
  change (trilinFormToModel (TangentSpace I x))
      (ccBilinConnectionDifferenceLoweredTrilin (I := I) g₀ V gA gB x)
        (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i)) = _
  rw [trilinFormToModel_apply, ccBilinConnectionDifferenceLoweredTrilin_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
private theorem trilinKernel_section_contMDiff
    (K : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hK : ∀ (Y0 Y1 Y2 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x₀ : M),
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x : M => K x (Y0 x) (Y1 x) (Y2 x)) x₀) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x
        ((Tensor0SBundle.tensor0SSpaceFiberContinuousLinearEquiv
          (I := I) 3 x).symm
          (trilinFormToModel (TangentSpace I x) (K x)))) := by
  classical
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x : M => ((Tensor0SBundle.tensor0SSpaceFiberContinuousLinearEquiv
        (I := I) 3 x).symm (trilinFormToModel (TangentSpace I x) (K x)) :
          Tensor0SBundle.Tensor0SSpace 3 I x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  refine (hK (Y (σ 0)) (Y (σ 1)) (Y (σ 2)) x₀).congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframe0 : e₁.symmL ℝ x (b (σ 0)) = (Y (σ 0)) x := by
    rw [hYx (σ 0), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    rw [Trivialization.basisAt, Module.Basis.map_apply, e₁.symmL_apply hx₁]
    rfl
  have hframe1 : e₁.symmL ℝ x (b (σ 1)) = (Y (σ 1)) x := by
    rw [hYx (σ 1), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    rw [Trivialization.basisAt, Module.Basis.map_apply, e₁.symmL_apply hx₁]
    rfl
  have hframe2 : e₁.symmL ℝ x (b (σ 2)) = (Y (σ 2)) x := by
    rw [hYx (σ 2), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    rw [Trivialization.basisAt, Module.Basis.map_apply, e₁.symmL_apply hx₁]
    rfl
  change (trilinFormToModel (TangentSpace I x) (K x))
      (fun j : Fin 3 => e₁.symmL ℝ x (b (σ j))) = _
  rw [trilinFormToModel_apply]
  rw [hframe0, hframe1, hframe2]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricConnectionDifferenceLoweredFib_contMDiff (gm gA gB : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x
        (metricConnectionDifferenceLoweredFib (I := I) gm gA gB x)) := by
  refine trilinKernel_section_contMDiff (I := I)
    (K := fun x => metricConnectionDifferenceLoweredTrilin (I := I) gm gA gB x) ?_
  intro Y0 Y1 Y2 x₀
  have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (PDE.DeTurck.connectionDifference (I := I) gA gB x (Y0 x) (Y1 x))) :=
    PDE.DeTurck.connectionDifference_contMDiff (I := I) gA gB Y0.contMDiff Y1.contMDiff
  have hscalar : ContMDiff I 𝓘(ℝ) ∞
      (fun x : M => gm.inner x
        (PDE.DeTurck.connectionDifference (I := I) gA gB x (Y0 x) (Y1 x)) (Y2 x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) gm
      ⟨fun x => PDE.DeTurck.connectionDifference (I := I) gA gB x (Y0 x) (Y1 x), hconn⟩ Y2
  refine (hscalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with x
  rw [metricConnectionDifferenceLoweredTrilin_apply]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ccBilinConnectionDifferenceLoweredFib_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x
        (ccBilinConnectionDifferenceLoweredFib (I := I) g₀ V gA gB x)) := by
  refine trilinKernel_section_contMDiff (I := I)
    (K := fun x => ccBilinConnectionDifferenceLoweredTrilin (I := I) g₀ V gA gB x) ?_
  intro Y0 Y1 Y2 x₀
  have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (PDE.DeTurck.connectionDifference (I := I) gA gB x (Y0 x) (Y1 x))) :=
    PDE.DeTurck.connectionDifference_contMDiff (I := I) gA gB Y0.contMDiff Y1.contMDiff
  have h_total : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun x : M => (⟨x, ccTensorBilinSymm (I := I) g₀ V x
        (PDE.DeTurck.connectionDifference (I := I) gA gB x (Y0 x) (Y1 x)) (Y2 x)⟩ :
          TotalSpace ℝ (Bundle.Trivial M ℝ))) x₀ :=
    (ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := id)
      (ccTensorBilinSymm_contMDiff (I := I) g₀ V).contMDiffOn hconn.contMDiffOn
      Y2.contMDiff.contMDiffOn x₀ (mem_univ x₀)).contMDiffAt univ_mem
  rw [Bundle.contMDiffAt_totalSpace] at h_total
  refine (h_total.2).congr_of_eventuallyEq ?_
  filter_upwards with x
  rw [ccBilinConnectionDifferenceLoweredTrilin_apply]
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
