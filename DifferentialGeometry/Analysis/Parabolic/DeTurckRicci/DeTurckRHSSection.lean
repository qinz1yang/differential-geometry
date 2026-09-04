import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.DeTurckRHS
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.LieDerivativePairing
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import DifferentialGeometry.Tensor.Mixed.Field
import DifferentialGeometry.Tensor.Multilinear.Curry.FiniteNorm
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field
open DifferentialGeometry.Tensor.Multilinear


open DifferentialGeometry.Analysis.Parabolic
noncomputable section


open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow


open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private def deTurckRHSModelFun (g_bg g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x).symm
    (biForm₂ToModel (TangentSpace I x) (deTurckRicciRHS (I := I) g_bg g x))

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem deTurckRHSModelFun_eval
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.eval (deTurckRHSModelFun (I := I) g_bg g x) v =
      deTurckRicciRHS (I := I) g_bg g x (v 0) (v 1) := by
  unfold deTurckRHSModelFun
  rw [Tensor0SSpace.eval_fiber_equiv_symm]
  exact biForm₂ToModel_apply (TangentSpace I x) (deTurckRicciRHS (I := I) g_bg g x) v

def deTurckRHSField (g_bg g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  letI := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => deTurckRHSModelFun (I := I) g_bg g x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M =>
          deTurckRicciRHS (I := I) g_bg g x
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (σ 0) x)
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (σ 1) x))
        (chartAt H x₀).source :=
      combine_smoothness_of_summands (I := I) g_bg g x₀ (σ 0) (σ 1)
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
    change Tensor0SSpace.eval (deTurckRHSModelFun (I := I) g_bg g x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [deTurckRHSModelFun_eval]
    rfl⟩

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem deTurckRHSField_eval
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.eval (deTurckRHSField (I := I) g_bg g x) v =
      deTurckRicciRHS (I := I) g_bg g x (v 0) (v 1) :=
  deTurckRHSModelFun_eval (I := I) g_bg g x v

def deTurckRHSMixedSection (g_bg g : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (deTurckRHSField (I := I) g_bg g)

def deTurckRHSSection (g_bg g : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 0 2 where
  toSection := deTurckRHSMixedSection (I := I) g_bg g
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem deTurckRHSSection_toSection
    (g_bg g : SmoothRiemannianMetric I M) :
    (deTurckRHSSection (I := I) g_bg g).toSection =
      deTurckRHSMixedSection (I := I) g_bg g := rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckRHSSection_eval
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.eval
        ((deTurckRHSSection (I := I) g_bg g).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      deTurckRicciRHS (I := I) g_bg g x (v 0) (v 1) := by
  classical
  rw [deTurckRHSSection_toSection]
  change Tensor0SSpace.eval
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (deTurckRHSField (I := I) g_bg g x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul,
    deTurckRHSField_eval]

end RicciFlow
end PDE
end DifferentialGeometry

end
