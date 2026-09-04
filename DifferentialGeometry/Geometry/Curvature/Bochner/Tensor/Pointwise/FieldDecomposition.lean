import DifferentialGeometry.Geometry.Curvature.Bochner.Tensor.Pointwise.Basic
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.SlotCurry.Reconstruction
import DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.TraceDiscrepancy
open DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] in
lemma pointwiseTensorCurv_eq_covGradRoughLapCurv_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    pointwiseTensorCurv (I := I) (M := M) g s S =
      covGradRoughLapCurvGen (I := I) (M := M) g s S := rfl

omit [CompactSpace M] in
lemma tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    tensor0SCurry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) +
        (covGradRoughLapTraceDiscrepancyGen (I := I) (M := M) g s S x w +
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
              (fun y : M => S.toSection y) x)
            (unitZeroSec (I := I) (M := M) x) -
          covGradRoughLapMovingFrameResidualGen (I := I) (M := M) g s S x w) := by
  rw [pointwiseTensorCurv_eq_covGradRoughLapCurv_gen (I := I) (M := M) g s S]
  rw [covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual_gen
    (I := I) (M := M) g s S x w]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorThirdOrderCurvatureDefect (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x +
        tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) from by
    rw [Tensor3rdCurv_eq_genuine_add_bracket (I := I) g 0 s
      (smoothExtensionTangent (I := I) x w) (fun y : M => S.toSection y) x]]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x +
        tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) +
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) from rfl]
  abel

noncomputable def genuineThirdCurvFieldFib
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (w : TangentSpace I x)
    (m : Fin s → E) : ℝ :=
  ∑ a : Fin n, g.inner x (e a) w •
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x (e a))
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x)) m

noncomputable def bracketThirdCurvFieldFib
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (w : TangentSpace I x)
    (m : Fin s → E) : ℝ :=
  ∑ a : Fin n, g.inner x (e a) w •
    Tensor0SSpace.toModel
      (covGradRoughLapTraceDiscrepancyGen (I := I) (M := M) g s S x (e a) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x (e a))
            (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) -
        covGradRoughLapMovingFrameResidualGen (I := I) (M := M) g s S x (e a)) m

omit [CompactSpace M] in
theorem pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (w : TangentSpace I x) (m : Fin s → E),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x))
              (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x w) m) =
          genuineThirdCurvFieldFib (I := I) (M := M) g s S x e w m +
            bracketThirdCurvFieldFib (I := I) (M := M) g s S x e w m := by
  classical
  obtain ⟨n, e, hn, horth, hrecon⟩ :=
    tensor0S_eq_sum_slot0_uncurry (I := I) (M := M) g s x
  refine ⟨n, e, hn, horth, fun w m => ?_⟩
  rw [hrecon
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) w m]
  rw [genuineThirdCurvFieldFib, bracketThirdCurvFieldFib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction
    (I := I) (M := M) g s S x (e a)]
  rw [Tensor0SSpace.toModel_add, add_apply, smul_add]

end Curvature
end Geometry
end DifferentialGeometry
