import DifferentialGeometry.Analysis.Convex.Tensor02PositiveSemidefiniteCone
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Endpoint
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open Tensor0SBundle
open DifferentialGeometry.Analysis.Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance parallelTensor02NormedAddCommGroup (x : M) :
    NormedAddCommGroup (Tensor0SSpace 2 I x) :=
  Tensor0SBundle.tensor0SSpace_normedAddCommGroup 2 x

private local instance parallelTensor02NormedSpace (x : M) :
    NormedSpace ℝ (Tensor0SSpace 2 I x) :=
  Tensor0SBundle.tensor0SSpace_normedSpace 2 x

private local instance parallelTensor02AddCommGroup (x : M) :
    AddCommGroup (Tensor0SSpace 2 I x) :=
  @NormedAddCommGroup.toAddCommGroup _ (parallelTensor02NormedAddCommGroup (I := I) x)

private local instance parallelTensor02Module (x : M) :
    Module ℝ (Tensor0SSpace 2 I x) :=
  @NormedSpace.toModule _ _ _ _ (parallelTensor02NormedSpace (I := I) x)

private local instance parallelTensor02TopologicalSpace (x : M) :
    TopologicalSpace (Tensor0SSpace 2 I x) :=
  @UniformSpace.toTopologicalSpace _
    (@PseudoMetricSpace.toUniformSpace _
      (@MetricSpace.toPseudoMetricSpace _
        (@NormedAddCommGroup.toMetricSpace _
          (parallelTensor02NormedAddCommGroup (I := I) x))))

noncomputable def parallelTransportTensor02CLEOnIcc [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) :
    Tensor0SSpace 2 I (γ 0) ≃L[ℝ] Tensor0SSpace 2 I (γ L) :=
  tensor02PullbackCLE (I := I) (M := M)
    (parallelTransportLinearEquivOnIcc (I := I) g γ hγ hL).symm

@[simp]
theorem parallelTransportTensor02CLEOnIcc_eval [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (A : Tensor0SSpace 2 I (γ 0))
    (v w : TangentSpace I (γ 0)) :
    eval02 (I := I) (M := M)
        (parallelTransportTensor02CLEOnIcc (I := I) g γ hγ hL A)
        (parallelTransportSectionOnIcc (I := I) g γ hγ hL v L)
        (parallelTransportSectionOnIcc (I := I) g γ hγ hL w L) =
      eval02 (I := I) (M := M) A v w := by
  let e := parallelTransportLinearEquivOnIcc (I := I) g γ hγ hL
  change eval02 (I := I) (M := M)
    (tensor02PullbackCLE (I := I) (M := M) e.symm A) (e v) (e w) = _
  rw [tensor02PullbackCLE_apply, tensor02PullbackCLM_eval]
  simp only [LinearEquiv.symm_apply_apply]

@[simp]
theorem parallelTransportTensor02CLEOnIcc_quad [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (A : Tensor0SSpace 2 I (γ 0))
    (v : TangentSpace I (γ 0)) :
    quad02 (I := I) (M := M)
        (parallelTransportTensor02CLEOnIcc (I := I) g γ hγ hL A)
        (parallelTransportSectionOnIcc (I := I) g γ hγ hL v L) =
      quad02 (I := I) (M := M) A v := by
  rw [← eval02_self, parallelTransportTensor02CLEOnIcc_eval, eval02_self]

theorem parallelTransportTensor02CLEOnIcc_mem_positiveSemidefiniteCone_iff
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (A : Tensor0SSpace 2 I (γ 0)) :
    parallelTransportTensor02CLEOnIcc (I := I) g γ hγ hL A ∈
        tensor02PositiveSemidefiniteCone (I := I) (M := M) ↔
      A ∈ tensor02PositiveSemidefiniteCone (I := I) (M := M) := by
  exact tensor02PullbackCLE_mem_positiveSemidefiniteCone_iff
    (I := I) (M := M)
      (parallelTransportLinearEquivOnIcc (I := I) g γ hγ hL).symm A

theorem tensor02PositiveSemidefiniteCone_map_parallelTransportOnIcc
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) :
    ((tensor02PositiveSemidefiniteCone (I := I) (M := M) :
      ProperCone ℝ (Tensor0SSpace 2 I (γ 0))).map
        (parallelTransportTensor02CLEOnIcc (I := I) g γ hγ hL).toContinuousLinearMap) =
      (tensor02PositiveSemidefiniteCone (I := I) (M := M) :
        ProperCone ℝ (Tensor0SSpace 2 I (γ L))) := by
  exact tensor02PositiveSemidefiniteCone_map_pullback (I := I) (M := M)
    (parallelTransportLinearEquivOnIcc (I := I) g γ hγ hL).symm

theorem tensor02PositiveSemidefinite_dualZeroFace_map_parallelTransportOnIcc
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v : TangentSpace I (γ 0)) :
    (((tensor02PositiveSemidefiniteCone (I := I) (M := M) :
      ProperCone ℝ (Tensor0SSpace 2 I (γ 0))).dualZeroFace
        (tensor02EvalSelfCLM (I := I) (M := M) v)).map
          (parallelTransportTensor02CLEOnIcc
            (I := I) g γ hγ hL).toContinuousLinearMap) =
      ((tensor02PositiveSemidefiniteCone (I := I) (M := M) :
        ProperCone ℝ (Tensor0SSpace 2 I (γ L))).dualZeroFace
          (tensor02EvalSelfCLM (I := I) (M := M)
            (parallelTransportLinearEquivOnIcc (I := I) g γ hγ hL v))) := by
  let e := parallelTransportLinearEquivOnIcc (I := I) g γ hγ hL
  change (((tensor02PositiveSemidefiniteCone (I := I) (M := M) :
      ProperCone ℝ (Tensor0SSpace 2 I (γ 0))).dualZeroFace
        (tensor02EvalSelfCLM (I := I) (M := M) v)).map
          (tensor02PullbackCLE (I := I) (M := M) e.symm).toContinuousLinearMap) =
    ((tensor02PositiveSemidefiniteCone (I := I) (M := M) :
      ProperCone ℝ (Tensor0SSpace 2 I (γ L))).dualZeroFace
        (tensor02EvalSelfCLM (I := I) (M := M) (e v)))
  simpa only [LinearEquiv.symm_apply_apply] using
    tensor02PositiveSemidefinite_dualZeroFace_map_pullback (I := I) (M := M)
      e.symm (e v)

theorem parallelTransportTensor02CLEOnIcc_mem_dualZeroFace_iff
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (A : Tensor0SSpace 2 I (γ 0))
    (v : TangentSpace I (γ 0)) :
    parallelTransportTensor02CLEOnIcc (I := I) g γ hγ hL A ∈
        (tensor02PositiveSemidefiniteCone (I := I) (M := M)).dualZeroFace
          (tensor02EvalSelfCLM (I := I) (M := M)
            (parallelTransportLinearEquivOnIcc (I := I) g γ hγ hL v)) ↔
      A ∈ (tensor02PositiveSemidefiniteCone (I := I) (M := M)).dualZeroFace
        (tensor02EvalSelfCLM (I := I) (M := M) v) := by
  rw [mem_tensor02PositiveSemidefinite_dualZeroFace,
    mem_tensor02PositiveSemidefinite_dualZeroFace]
  constructor
  · rintro ⟨hA, hv⟩
    refine ⟨parallelTransportTensor02CLEOnIcc_mem_positiveSemidefiniteCone_iff
      (I := I) g γ hγ hL A |>.mp hA, ?_⟩
    rw [mem_twoTensorLeftKernel_iff] at hv ⊢
    intro w
    have h := hv (parallelTransportLinearEquivOnIcc (I := I) g γ hγ hL w)
    rw [← parallelTransportTensor02CLEOnIcc_eval (I := I) g γ hγ hL A v w]
    exact h
  · rintro ⟨hA, hv⟩
    refine ⟨parallelTransportTensor02CLEOnIcc_mem_positiveSemidefiniteCone_iff
      (I := I) g γ hγ hL A |>.mpr hA, ?_⟩
    rw [mem_twoTensorLeftKernel_iff] at hv ⊢
    intro w
    let e := parallelTransportLinearEquivOnIcc (I := I) g γ hγ hL
    have h := hv (e.symm w)
    change eval02 (I := I) (M := M)
      (parallelTransportTensor02CLEOnIcc (I := I) g γ hγ hL A) (e v) w = 0
    calc
      _ = eval02 (I := I) (M := M)
          (parallelTransportTensor02CLEOnIcc (I := I) g γ hγ hL A)
          (e v) (e (e.symm w)) := by rw [e.apply_symm_apply]
      _ = eval02 (I := I) (M := M) A v (e.symm w) :=
        parallelTransportTensor02CLEOnIcc_eval (I := I) g γ hγ hL A v (e.symm w)
      _ = 0 := h

noncomputable def parallelTransportTensor02CLEBetween [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b) :
    Tensor0SSpace 2 I (γ a) ≃L[ℝ] Tensor0SSpace 2 I (γ b) :=
  tensor02PullbackCLE (I := I) (M := M)
    (parallelTransportLinearEquivBetween (I := I) g γ hγ hab).symm

@[simp]
theorem parallelTransportTensor02CLEBetween_eval [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b) (A : Tensor0SSpace 2 I (γ a))
    (v w : TangentSpace I (γ a)) :
    eval02 (I := I) (M := M)
        (parallelTransportTensor02CLEBetween (I := I) g γ hγ hab A)
        (parallelTransportLinearEquivBetween (I := I) g γ hγ hab v)
        (parallelTransportLinearEquivBetween (I := I) g γ hγ hab w) =
      eval02 (I := I) (M := M) A v w := by
  let e := parallelTransportLinearEquivBetween (I := I) g γ hγ hab
  change eval02 (I := I) (M := M)
    (tensor02PullbackCLE (I := I) (M := M) e.symm A) (e v) (e w) = _
  rw [tensor02PullbackCLE_apply, tensor02PullbackCLM_eval]
  simp only [LinearEquiv.symm_apply_apply]

@[simp]
theorem parallelTransportTensor02CLEBetween_quad [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b) (A : Tensor0SSpace 2 I (γ a))
    (v : TangentSpace I (γ a)) :
    quad02 (I := I) (M := M)
        (parallelTransportTensor02CLEBetween (I := I) g γ hγ hab A)
        (parallelTransportLinearEquivBetween (I := I) g γ hγ hab v) =
      quad02 (I := I) (M := M) A v := by
  rw [← eval02_self, parallelTransportTensor02CLEBetween_eval, eval02_self]

theorem parallelTransportTensor02CLEBetween_mem_positiveSemidefiniteCone_iff
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b) (A : Tensor0SSpace 2 I (γ a)) :
    parallelTransportTensor02CLEBetween (I := I) g γ hγ hab A ∈
        tensor02PositiveSemidefiniteCone (I := I) (M := M) ↔
      A ∈ tensor02PositiveSemidefiniteCone (I := I) (M := M) :=
  tensor02PullbackCLE_mem_positiveSemidefiniteCone_iff (I := I) (M := M)
    (parallelTransportLinearEquivBetween (I := I) g γ hγ hab).symm A

theorem tensor02PositiveSemidefiniteCone_map_parallelTransportBetween
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b) :
    ((tensor02PositiveSemidefiniteCone (I := I) (M := M) :
      ProperCone ℝ (Tensor0SSpace 2 I (γ a))).map
        (parallelTransportTensor02CLEBetween
          (I := I) g γ hγ hab).toContinuousLinearMap) =
      (tensor02PositiveSemidefiniteCone (I := I) (M := M) :
        ProperCone ℝ (Tensor0SSpace 2 I (γ b))) :=
  tensor02PositiveSemidefiniteCone_map_pullback (I := I) (M := M)
    (parallelTransportLinearEquivBetween (I := I) g γ hγ hab).symm

theorem twoTensorLeftKernel_map_parallelTransportBetween [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b) (A : Tensor0SSpace 2 I (γ a)) :
    (twoTensorLeftKernel (I := I) (M := M) A).map
        (parallelTransportLinearEquivBetween (I := I) g γ hγ hab).toLinearMap =
      twoTensorLeftKernel (I := I) (M := M)
        (parallelTransportTensor02CLEBetween (I := I) g γ hγ hab A) := by
  let e := parallelTransportLinearEquivBetween (I := I) g γ hγ hab
  change (twoTensorLeftKernel (I := I) (M := M) A).map e.toLinearMap = _
  apply Submodule.ext
  intro w
  rw [Submodule.mem_map_equiv]
  rw [mem_twoTensorLeftKernel_iff, mem_twoTensorLeftKernel_iff]
  constructor
  · intro hw z
    have h := hw (e.symm z)
    have heval : eval02 (I := I) (M := M)
        (parallelTransportTensor02CLEBetween (I := I) g γ hγ hab A)
          (e (e.symm w)) (e (e.symm z)) =
        eval02 (I := I) (M := M) A (e.symm w) (e.symm z) :=
      parallelTransportTensor02CLEBetween_eval
        (I := I) g γ hγ hab A (e.symm w) (e.symm z)
    simpa only [e.apply_symm_apply] using heval.trans h
  · intro hw z
    have h := hw (e z)
    have heval : eval02 (I := I) (M := M)
        (parallelTransportTensor02CLEBetween (I := I) g γ hγ hab A)
          (e (e.symm w)) (e z) =
        eval02 (I := I) (M := M) A (e.symm w) z :=
      parallelTransportTensor02CLEBetween_eval
        (I := I) g γ hγ hab A (e.symm w) z
    have heval' : eval02 (I := I) (M := M)
        (parallelTransportTensor02CLEBetween (I := I) g γ hγ hab A) w (e z) =
        eval02 (I := I) (M := M) A (e.symm w) z := by
      simpa only [e.apply_symm_apply] using heval
    exact heval'.symm.trans h

theorem twoTensorNullSpace_finrank_eq_parallelTransportBetween [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b) (A : Tensor0SSpace 2 I (γ a)) :
    Module.finrank ℝ (twoTensorLeftKernel (I := I) (M := M)
        (parallelTransportTensor02CLEBetween (I := I) g γ hγ hab A)) =
      Module.finrank ℝ (twoTensorLeftKernel (I := I) (M := M) A) := by
  let e := parallelTransportLinearEquivBetween (I := I) g γ hγ hab
  have hmap := twoTensorLeftKernel_map_parallelTransportBetween
    (I := I) g γ hγ hab A
  rw [← hmap]
  exact LinearEquiv.finrank_map_eq e (twoTensorLeftKernel (I := I) (M := M) A)

theorem tensor02PositiveSemidefinite_dualZeroFace_map_parallelTransportBetween
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b) (v : TangentSpace I (γ a)) :
    (((tensor02PositiveSemidefiniteCone (I := I) (M := M) :
      ProperCone ℝ (Tensor0SSpace 2 I (γ a))).dualZeroFace
        (tensor02EvalSelfCLM (I := I) (M := M) v)).map
          (parallelTransportTensor02CLEBetween
            (I := I) g γ hγ hab).toContinuousLinearMap) =
      ((tensor02PositiveSemidefiniteCone (I := I) (M := M) :
        ProperCone ℝ (Tensor0SSpace 2 I (γ b))).dualZeroFace
          (tensor02EvalSelfCLM (I := I) (M := M)
            (parallelTransportLinearEquivBetween (I := I) g γ hγ hab v))) := by
  let e := parallelTransportLinearEquivBetween (I := I) g γ hγ hab
  change (((tensor02PositiveSemidefiniteCone (I := I) (M := M) :
      ProperCone ℝ (Tensor0SSpace 2 I (γ a))).dualZeroFace
        (tensor02EvalSelfCLM (I := I) (M := M) v)).map
          (tensor02PullbackCLE (I := I) (M := M) e.symm).toContinuousLinearMap) =
    ((tensor02PositiveSemidefiniteCone (I := I) (M := M) :
      ProperCone ℝ (Tensor0SSpace 2 I (γ b))).dualZeroFace
        (tensor02EvalSelfCLM (I := I) (M := M) (e v)))
  simpa only [LinearEquiv.symm_apply_apply] using
    tensor02PositiveSemidefinite_dualZeroFace_map_pullback (I := I) (M := M)
      e.symm (e v)

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
