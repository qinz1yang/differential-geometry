import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.Unit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]

private local instance tensor02NormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  Tensor0SBundle.tensor0SSpace_normedAddCommGroup 2 x

private local instance tensor02NormedSpace (x : M) :
    NormedSpace Real
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  Tensor0SBundle.tensor0SSpace_normedSpace 2 x

private local instance tensor02AddCommGroup (x : M) :
    AddCommGroup
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  @NormedAddCommGroup.toAddCommGroup _ (tensor02NormedAddCommGroup (I := I) x)

private local instance tensor02Module (x : M) :
    Module Real
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  @NormedSpace.toModule _ _ _ _ (tensor02NormedSpace (I := I) x)

private local instance tensor02TopologicalSpace (x : M) :
    TopologicalSpace
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  @UniformSpace.toTopologicalSpace _
    (@PseudoMetricSpace.toUniformSpace _
      (@MetricSpace.toPseudoMetricSpace _
        (@NormedAddCommGroup.toMetricSpace _ (tensor02NormedAddCommGroup (I := I) x))))

noncomputable def tensor02EvalCLM {x : M} (v w : TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x →L[Real] Real :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A ↦ eval02 (I := I) (M := M) A v w
    map_add' := by
      intro A B
      rfl
    map_smul' := by
      intro c A
      rfl }

@[simp]
theorem tensor02EvalCLM_apply {x : M} (v w : TangentSpace I x)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    tensor02EvalCLM (I := I) (M := M) v w A = eval02 (I := I) (M := M) A v w :=
  rfl

noncomputable def tensor02EvalSelfCLM {x : M} (v : TangentSpace I x) :
    StrongDual Real
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A ↦ quad02 (I := I) (M := M) A v
    map_add' := by
      intro A B
      rfl
    map_smul' := by
      intro c A
      rfl }

@[simp]
theorem tensor02EvalSelfCLM_apply {x : M} (v : TangentSpace I x)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    tensor02EvalSelfCLM (I := I) (M := M) v A = quad02 (I := I) (M := M) A v :=
  rfl

private noncomputable def tensor02PullbackValue {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace 2 I y) : Tensor0SSpace 2 I x :=
  Tensor0SSpace.ofModel (I := I) (x := x)
    ((Tensor0SSpace.toModel A).compContinuousLinearMap
      (fun _ : Fin 2 ↦ LinearMap.toContinuousLinearMap e.toLinearMap))

private theorem tensor02PullbackValue_eval {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace 2 I y) (v w : TangentSpace I x) :
    eval02 (I := I) (M := M) (tensor02PullbackValue (I := I) (M := M) e A) v w =
      eval02 (I := I) (M := M) A (e v) (e w) := by
  change
    ((Tensor0SSpace.toModel A).compContinuousLinearMap
      (fun _ : Fin 2 ↦ LinearMap.toContinuousLinearMap e.toLinearMap))
        (fun i : Fin 2 ↦ if i = 0 then v else w) = _
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change A (fun i : Fin 2 ↦ e (if i = 0 then v else w)) = _
  congr 1
  funext i
  fin_cases i <;> simp

noncomputable def tensor02PullbackCLM {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    Tensor0SSpace 2 I y →L[Real] Tensor0SSpace 2 I x :=
  LinearMap.toContinuousLinearMap {
    toFun := tensor02PullbackValue (I := I) (M := M) e
    map_add' := by
      intro A B
      apply tensor0SSpace_ext 2 x
      intro m
      have hm : m = fun i ↦ if i = 0 then m 0 else m 1 := by
        funext i
        fin_cases i <;> simp
      rw [hm]
      change eval02 (I := I) (M := M)
        (tensor02PullbackValue (I := I) (M := M) e (A + B)) (m 0) (m 1) =
        eval02 (I := I) (M := M)
          (tensor02PullbackValue (I := I) (M := M) e A) (m 0) (m 1) +
        eval02 (I := I) (M := M)
          (tensor02PullbackValue (I := I) (M := M) e B) (m 0) (m 1)
      rw [tensor02PullbackValue_eval, tensor02PullbackValue_eval,
        tensor02PullbackValue_eval]
      rfl
    map_smul' := by
      intro (c : Real) A
      apply tensor0SSpace_ext 2 x
      intro m
      have hm : m = fun i ↦ if i = 0 then m 0 else m 1 := by
        funext i
        fin_cases i <;> simp
      rw [hm]
      change eval02 (I := I) (M := M)
        (tensor02PullbackValue (I := I) (M := M) e (c • A)) (m 0) (m 1) =
        c • eval02 (I := I) (M := M)
          (tensor02PullbackValue (I := I) (M := M) e A) (m 0) (m 1)
      rw [tensor02PullbackValue_eval, tensor02PullbackValue_eval]
      rfl }

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
    Tensor0SSpace 2 I y ≃L[Real] Tensor0SSpace 2 I x where
  toFun := tensor02PullbackCLM (I := I) (M := M) e
  invFun := tensor02PullbackCLM (I := I) (M := M) e.symm
  left_inv A := by
    apply tensor0SSpace_ext 2 y
    intro m
    have hm : m = fun i ↦ if i = 0 then m 0 else m 1 := by
      funext i
      fin_cases i <;> simp
    rw [hm]
    change eval02 (I := I) (M := M)
      (tensor02PullbackCLM (I := I) (M := M) e.symm
        (tensor02PullbackCLM (I := I) (M := M) e A)) (m 0) (m 1) =
      eval02 (I := I) (M := M) A (m 0) (m 1)
    rw [tensor02PullbackCLM_eval, tensor02PullbackCLM_eval]
    simp
  right_inv A := by
    apply tensor0SSpace_ext 2 x
    intro m
    have hm : m = fun i ↦ if i = 0 then m 0 else m 1 := by
      funext i
      fin_cases i <;> simp
    rw [hm]
    change eval02 (I := I) (M := M)
      (tensor02PullbackCLM (I := I) (M := M) e
        (tensor02PullbackCLM (I := I) (M := M) e.symm A)) (m 0) (m 1) =
      eval02 (I := I) (M := M) A (m 0) (m 1)
    rw [tensor02PullbackCLM_eval, tensor02PullbackCLM_eval]
    simp
  map_add' A B := (tensor02PullbackCLM (I := I) (M := M) e).map_add A B
  map_smul' c A := (tensor02PullbackCLM (I := I) (M := M) e).map_smul c A
  continuous_toFun := (tensor02PullbackCLM (I := I) (M := M) e).continuous
  continuous_invFun := (tensor02PullbackCLM (I := I) (M := M) e.symm).continuous

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
