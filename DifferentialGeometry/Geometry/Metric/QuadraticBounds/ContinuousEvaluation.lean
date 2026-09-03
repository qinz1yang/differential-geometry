import DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit
import DifferentialGeometry.Tensor.RSTensor.Pullback

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]

noncomputable def tensor02EvalCLM {x : M} (v w : TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x →L[Real] Real :=
  tensor0SEvalCLM (I := I) (M := M) (fun i ↦ if i = 0 then v else w)

@[simp]
theorem tensor02EvalCLM_apply {x : M} (v w : TangentSpace I x)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    tensor02EvalCLM (I := I) (M := M) v w A = eval02 (I := I) (M := M) A v w :=
  rfl

noncomputable def tensor02EvalSelfCLM {x : M} (v : TangentSpace I x) :
    StrongDual Real
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  tensor0SEvalCLM (I := I) (M := M) (fun _ ↦ v)

@[simp]
theorem tensor02EvalSelfCLM_apply {x : M} (v : TangentSpace I x)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    tensor02EvalSelfCLM (I := I) (M := M) v A = quad02 (I := I) (M := M) A v :=
  rfl

private noncomputable def tensor02PullbackValue {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace 2 I y) : Tensor0SSpace 2 I x :=
  tensor0SPullbackCLM (I := I) (M := M) 2 e A

private theorem tensor02PullbackValue_eval {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace 2 I y) (v w : TangentSpace I x) :
    eval02 (I := I) (M := M) (tensor02PullbackValue (I := I) (M := M) e A) v w =
      eval02 (I := I) (M := M) A (e v) (e w) := by
  unfold tensor02PullbackValue eval02
  rw [tensor0SPullbackCLM_apply]
  change A (fun i : Fin 2 ↦ e (if i = 0 then v else w)) = _
  congr 1
  funext i
  fin_cases i <;> simp

noncomputable def tensor02PullbackCLM {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    Tensor0SSpace 2 I y →L[Real] Tensor0SSpace 2 I x :=
  tensor0SPullbackCLM (I := I) (M := M) 2 e

@[simp]
theorem tensor02PullbackCLM_eval {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace 2 I y) (v w : TangentSpace I x) :
    eval02 (I := I) (M := M) (tensor02PullbackCLM (I := I) (M := M) e A) v w =
      eval02 (I := I) (M := M) A (e v) (e w) := by
  exact tensor02PullbackValue_eval (I := I) (M := M) e A v w

@[simp]
theorem tensor02PullbackCLM_quad {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace 2 I y) (v : TangentSpace I x) :
    quad02 (I := I) (M := M) (tensor02PullbackCLM (I := I) (M := M) e A) v =
      quad02 (I := I) (M := M) A (e v) := by
  rw [← eval02_self, tensor02PullbackCLM_eval, eval02_self]

noncomputable def tensor02PullbackCLE {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    Tensor0SSpace 2 I y ≃L[Real] Tensor0SSpace 2 I x :=
  tensor0SPullbackCLE (I := I) (M := M) 2 e

@[simp]
theorem tensor02PullbackCLE_apply {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) (A : Tensor0SSpace 2 I y) :
    tensor02PullbackCLE (I := I) (M := M) e A =
      tensor02PullbackCLM (I := I) (M := M) e A := by
  apply tensor0SSpace_ext 2 x
  intro m
  rfl

@[simp]
theorem tensor02PullbackCLE_symm_apply {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) (A : Tensor0SSpace 2 I x) :
    (tensor02PullbackCLE (I := I) (M := M) e).symm A =
      tensor02PullbackCLM (I := I) (M := M) e.symm A := by
  apply tensor0SSpace_ext 2 y
  intro m
  rfl

end DifferentialGeometry
