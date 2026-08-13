import DifferentialGeometry.Analysis.Convex.Tensor04SectionalNonnegativeCone
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Endpoint

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

private local instance parallelTensor04NormedAddCommGroup (x : M) :
    NormedAddCommGroup (Tensor0SSpace 4 I x) :=
  Tensor0SBundle.tensor0SSpace_normedAddCommGroup 4 x

private local instance parallelTensor04NormedSpace (x : M) :
    NormedSpace ℝ (Tensor0SSpace 4 I x) :=
  Tensor0SBundle.tensor0SSpace_normedSpace 4 x

private local instance parallelTensor04AddCommGroup (x : M) :
    AddCommGroup (Tensor0SSpace 4 I x) :=
  @NormedAddCommGroup.toAddCommGroup _ (parallelTensor04NormedAddCommGroup (I := I) x)

private local instance parallelTensor04Module (x : M) :
    Module ℝ (Tensor0SSpace 4 I x) :=
  @NormedSpace.toModule _ _ _ _ (parallelTensor04NormedSpace (I := I) x)

private local instance parallelTensor04TopologicalSpace (x : M) :
    TopologicalSpace (Tensor0SSpace 4 I x) :=
  @UniformSpace.toTopologicalSpace _
    (@PseudoMetricSpace.toUniformSpace _
      (@MetricSpace.toPseudoMetricSpace _
        (@NormedAddCommGroup.toMetricSpace _
          (parallelTensor04NormedAddCommGroup (I := I) x))))

noncomputable def parallelTransportTensor04CLEOnIcc [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) gamma)
    {L : ℝ} (hL : 0 < L) :
    Tensor0SSpace 4 I (gamma 0) ≃L[ℝ] Tensor0SSpace 4 I (gamma L) :=
  tensor0SPullbackCLE (I := I) (M := M) 4
    (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL).symm

@[simp]
theorem parallelTransportTensor04CLEOnIcc_sectionalEval [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) gamma)
    {L : ℝ} (hL : 0 < L) (A : Tensor0SSpace 4 I (gamma 0))
    (v w : TangentSpace I (gamma 0)) :
    tensor04SectionalEval (I := I) (M := M)
        (parallelTransportTensor04CLEOnIcc (I := I) g gamma hgamma hL A)
        (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL v)
        (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL w) =
      tensor04SectionalEval (I := I) (M := M) A v w := by
  let e := parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL
  change tensor04SectionalEval (I := I) (M := M)
      (tensor0SPullbackCLE (I := I) (M := M) 4 e.symm A) (e v) (e w) = _
  rw [tensor04SectionalEval_pullback]
  simp

theorem parallelTransportTensor04CLEOnIcc_mem_sectionalNonnegativeCone_iff
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) gamma)
    {L : ℝ} (hL : 0 < L) (A : Tensor0SSpace 4 I (gamma 0)) :
    parallelTransportTensor04CLEOnIcc (I := I) g gamma hgamma hL A ∈
        tensor04SectionalNonnegativeCone (I := I) (M := M) ↔
      A ∈ tensor04SectionalNonnegativeCone (I := I) (M := M) :=
  tensor0SPullbackCLE_mem_sectionalNonnegativeCone_iff (I := I) (M := M)
    (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL).symm A

theorem tensor04SectionalNonnegativeCone_map_parallelTransportOnIcc
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) gamma)
    {L : ℝ} (hL : 0 < L) :
    ((tensor04SectionalNonnegativeCone (I := I) (M := M) :
      ProperCone ℝ (Tensor0SSpace 4 I (gamma 0))).map
        (parallelTransportTensor04CLEOnIcc
          (I := I) g gamma hgamma hL).toContinuousLinearMap) =
      (tensor04SectionalNonnegativeCone (I := I) (M := M) :
        ProperCone ℝ (Tensor0SSpace 4 I (gamma L))) :=
  tensor04SectionalNonnegativeCone_map_pullback (I := I) (M := M)
    (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL).symm

theorem tensor04SectionalNonnegative_dualZeroFace_map_parallelTransportOnIcc
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) gamma)
    {L : ℝ} (hL : 0 < L) (v w : TangentSpace I (gamma 0)) :
    (((tensor04SectionalNonnegativeCone (I := I) (M := M) :
      ProperCone ℝ (Tensor0SSpace 4 I (gamma 0))).dualZeroFace
        (tensor04SectionalEvalCLM (I := I) (M := M) v w)).map
          (parallelTransportTensor04CLEOnIcc
            (I := I) g gamma hgamma hL).toContinuousLinearMap) =
      ((tensor04SectionalNonnegativeCone (I := I) (M := M) :
        ProperCone ℝ (Tensor0SSpace 4 I (gamma L))).dualZeroFace
          (tensor04SectionalEvalCLM (I := I) (M := M)
            (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL v)
            (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL w))) := by
  let e := parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL
  change (((tensor04SectionalNonnegativeCone (I := I) (M := M) :
      ProperCone ℝ (Tensor0SSpace 4 I (gamma 0))).dualZeroFace
        (tensor04SectionalEvalCLM (I := I) (M := M) v w)).map
          (tensor0SPullbackCLE (I := I) (M := M) 4 e.symm).toContinuousLinearMap) =
    ((tensor04SectionalNonnegativeCone (I := I) (M := M) :
      ProperCone ℝ (Tensor0SSpace 4 I (gamma L))).dualZeroFace
        (tensor04SectionalEvalCLM (I := I) (M := M) (e v) (e w)))
  simpa using tensor04SectionalNonnegative_dualZeroFace_map_pullback
    (I := I) (M := M) e.symm (e v) (e w)

theorem parallelTransportTensor04CLEOnIcc_mem_dualZeroFace_iff
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) gamma)
    {L : ℝ} (hL : 0 < L) (A : Tensor0SSpace 4 I (gamma 0))
    (v w : TangentSpace I (gamma 0)) :
    parallelTransportTensor04CLEOnIcc (I := I) g gamma hgamma hL A ∈
        (tensor04SectionalNonnegativeCone (I := I) (M := M)).dualZeroFace
          (tensor04SectionalEvalCLM (I := I) (M := M)
            (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL v)
            (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL w)) ↔
      A ∈ (tensor04SectionalNonnegativeCone (I := I) (M := M)).dualZeroFace
        (tensor04SectionalEvalCLM (I := I) (M := M) v w) := by
  rw [mem_tensor04SectionalNonnegative_dualZeroFace,
    mem_tensor04SectionalNonnegative_dualZeroFace]
  rw [parallelTransportTensor04CLEOnIcc_mem_sectionalNonnegativeCone_iff]
  rw [parallelTransportTensor04CLEOnIcc_sectionalEval]

noncomputable def parallelTransportTensor04CLEBetween [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) gamma)
    {a b : ℝ} (hab : a < b) :
    Tensor0SSpace 4 I (gamma a) ≃L[ℝ] Tensor0SSpace 4 I (gamma b) :=
  tensor0SPullbackCLE (I := I) (M := M) 4
    (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab).symm

@[simp]
theorem parallelTransportTensor04CLEBetween_sectionalEval [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) gamma)
    {a b : ℝ} (hab : a < b) (A : Tensor0SSpace 4 I (gamma a))
    (v w : TangentSpace I (gamma a)) :
    tensor04SectionalEval (I := I) (M := M)
        (parallelTransportTensor04CLEBetween (I := I) g gamma hgamma hab A)
        (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab v)
        (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab w) =
      tensor04SectionalEval (I := I) (M := M) A v w := by
  let e := parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab
  change tensor04SectionalEval (I := I) (M := M)
      (tensor0SPullbackCLE (I := I) (M := M) 4 e.symm A) (e v) (e w) = _
  rw [tensor04SectionalEval_pullback]
  simp

theorem parallelTransportTensor04CLEBetween_mem_sectionalNonnegativeCone_iff
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) gamma)
    {a b : ℝ} (hab : a < b) (A : Tensor0SSpace 4 I (gamma a)) :
    parallelTransportTensor04CLEBetween (I := I) g gamma hgamma hab A ∈
        tensor04SectionalNonnegativeCone (I := I) (M := M) ↔
      A ∈ tensor04SectionalNonnegativeCone (I := I) (M := M) :=
  tensor0SPullbackCLE_mem_sectionalNonnegativeCone_iff (I := I) (M := M)
    (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab).symm A

theorem tensor04SectionalNonnegativeCone_map_parallelTransportBetween
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) gamma)
    {a b : ℝ} (hab : a < b) :
    ((tensor04SectionalNonnegativeCone (I := I) (M := M) :
      ProperCone ℝ (Tensor0SSpace 4 I (gamma a))).map
        (parallelTransportTensor04CLEBetween
          (I := I) g gamma hgamma hab).toContinuousLinearMap) =
      (tensor04SectionalNonnegativeCone (I := I) (M := M) :
        ProperCone ℝ (Tensor0SSpace 4 I (gamma b))) :=
  tensor04SectionalNonnegativeCone_map_pullback (I := I) (M := M)
    (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab).symm

theorem tensor04SectionalNonnegative_dualZeroFace_map_parallelTransportBetween
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) gamma)
    {a b : ℝ} (hab : a < b) (v w : TangentSpace I (gamma a)) :
    (((tensor04SectionalNonnegativeCone (I := I) (M := M) :
      ProperCone ℝ (Tensor0SSpace 4 I (gamma a))).dualZeroFace
        (tensor04SectionalEvalCLM (I := I) (M := M) v w)).map
          (parallelTransportTensor04CLEBetween
            (I := I) g gamma hgamma hab).toContinuousLinearMap) =
      ((tensor04SectionalNonnegativeCone (I := I) (M := M) :
        ProperCone ℝ (Tensor0SSpace 4 I (gamma b))).dualZeroFace
          (tensor04SectionalEvalCLM (I := I) (M := M)
            (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab v)
            (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab w))) := by
  let e := parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab
  change (((tensor04SectionalNonnegativeCone (I := I) (M := M) :
      ProperCone ℝ (Tensor0SSpace 4 I (gamma a))).dualZeroFace
        (tensor04SectionalEvalCLM (I := I) (M := M) v w)).map
          (tensor0SPullbackCLE (I := I) (M := M) 4 e.symm).toContinuousLinearMap) =
    ((tensor04SectionalNonnegativeCone (I := I) (M := M) :
      ProperCone ℝ (Tensor0SSpace 4 I (gamma b))).dualZeroFace
        (tensor04SectionalEvalCLM (I := I) (M := M) (e v) (e w)))
  simpa using tensor04SectionalNonnegative_dualZeroFace_map_pullback
    (I := I) (M := M) e.symm (e v) (e w)

theorem parallelTransportTensor04CLEBetween_mem_dualZeroFace_iff
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) gamma)
    {a b : ℝ} (hab : a < b) (A : Tensor0SSpace 4 I (gamma a))
    (v w : TangentSpace I (gamma a)) :
    parallelTransportTensor04CLEBetween (I := I) g gamma hgamma hab A ∈
        (tensor04SectionalNonnegativeCone (I := I) (M := M)).dualZeroFace
          (tensor04SectionalEvalCLM (I := I) (M := M)
            (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab v)
            (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab w)) ↔
      A ∈ (tensor04SectionalNonnegativeCone (I := I) (M := M)).dualZeroFace
        (tensor04SectionalEvalCLM (I := I) (M := M) v w) := by
  rw [mem_tensor04SectionalNonnegative_dualZeroFace,
    mem_tensor04SectionalNonnegative_dualZeroFace]
  rw [parallelTransportTensor04CLEBetween_mem_sectionalNonnegativeCone_iff]
  rw [parallelTransportTensor04CLEBetween_sectionalEval]

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
