import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricPullback

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature (vec2)
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem tensor0SPullbackCLE_metricTensor0S
    (gSource gTarget : SmoothRiemannianMetric I M) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (hiso : ∀ u v, gTarget.inner y (e u) (e v) = gSource.inner x u v) :
    tensor0SPullbackCLE (I := I) (M := M) 2 e (metricTensor0S gTarget y) =
      metricTensor0S gSource x := by
  apply tensor0SSpace_ext 2 x
  intro v
  simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply,
    metricTensor0S_apply, hiso]

theorem metricTracePair0SAt_tensor0SPullbackCLE
    (gSource gTarget : SmoothRiemannianMetric I M) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (hiso : ∀ u v, gTarget.inner y (e u) (e v) = gSource.inner x u v)
    (A : Tensor0SSpace 2 I y) :
    metricTracePair0SAt gSource (tensor0SPullbackCLE (I := I) (M := M) 2 e A) =
      metricTracePair0SAt gTarget A := by
  unfold metricTracePair0SAt
  rw [← tensor0SPullbackCLE_metricTensor0S gSource gTarget e hiso]
  exact Tensor0SBundle.inner0S_tensor0SPullbackCLE gSource gTarget x y 2 e hiso _ A

private theorem freezeFirstTwo0S_tensor0SPullbackCLE
    {s : Nat} {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace (s + 2) I y) (tail : Fin s → TangentSpace I x) :
    freezeFirstTwo0S (tensor0SPullbackCLE (I := I) (M := M) (s + 2) e A) tail =
      tensor0SPullbackCLE (I := I) (M := M) 2 e
        (freezeFirstTwo0S A (fun i => e (tail i))) := by
  apply tensor0SSpace_ext 2 x
  intro v
  have hv : v = vec2 (I := I) (v 0) (v 1) := by
    funext i
    fin_cases i <;> rfl
  rw [hv, freezeFirstTwo0S_apply, tensor0SPullbackCLE_apply,
    tensor0SPullbackCLM_apply, tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply]
  have he : (fun i => e (vec2 (I := I) (v 0) (v 1) i)) =
      vec2 (I := I) (e (v 0)) (e (v 1)) := by
    funext i
    fin_cases i <;> rfl
  rw [he, freezeFirstTwo0S_apply]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl

theorem metricTraceFirstTwo0SAt_tensor0SPullbackCLE
    (gSource gTarget : SmoothRiemannianMetric I M) {s : Nat} {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (hiso : ∀ u v, gTarget.inner y (e u) (e v) = gSource.inner x u v)
    (A : Tensor0SSpace (s + 2) I y) (tail : Fin s → TangentSpace I x) :
    metricTraceFirstTwo0SAt gSource
        (tensor0SPullbackCLE (I := I) (M := M) (s + 2) e A) tail =
      metricTraceFirstTwo0SAt gTarget A (fun i => e (tail i)) := by
  unfold metricTraceFirstTwo0SAt
  rw [freezeFirstTwo0S_tensor0SPullbackCLE,
    metricTracePair0SAt_tensor0SPullbackCLE gSource gTarget e hiso]

theorem metricTraceFirstTwo0STensor_tensor0SPullbackCLE
    (gSource gTarget : SmoothRiemannianMetric I M) {s : Nat} {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (hiso : ∀ u v, gTarget.inner y (e u) (e v) = gSource.inner x u v)
    (A : Tensor0SSpace (s + 2) I y) :
    metricTraceFirstTwo0STensor gSource
        (tensor0SPullbackCLE (I := I) (M := M) (s + 2) e A) =
      tensor0SPullbackCLE (I := I) (M := M) s e
        (metricTraceFirstTwo0STensor gTarget A) := by
  apply tensor0SSpace_ext s x
  intro tail
  simp only [metricTraceFirstTwo0STensor_apply, tensor0SPullbackCLE_apply,
    tensor0SPullbackCLM_apply]
  exact metricTraceFirstTwo0SAt_tensor0SPullbackCLE gSource gTarget e hiso A tail

theorem roughLap0STensor_tensor0SPullbackCLE
    (gSource gTarget : SmoothRiemannianMetric I M) {s : Nat} {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (hiso : ∀ u v, gTarget.inner y (e u) (e v) = gSource.inner x u v)
    (A : Tensor0SSpace (s + 2) I y) :
    roughLap0STensor gSource
        (tensor0SPullbackCLE (I := I) (M := M) (s + 2) e A) =
      tensor0SPullbackCLE (I := I) (M := M) s e (roughLap0STensor gTarget A) :=
  metricTraceFirstTwo0STensor_tensor0SPullbackCLE gSource gTarget e hiso A

end DifferentialGeometry.Geometry.Operator
