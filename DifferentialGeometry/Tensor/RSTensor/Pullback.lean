import DifferentialGeometry.Tensor.RSTensor.Defs

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

private local instance pullbackTensor0SNormedAddCommGroup (s : ℕ) (x : M) :
    NormedAddCommGroup (Tensor0SSpace s I x) :=
  Tensor0SBundle.tensor0SSpace_normedAddCommGroup s x

private local instance pullbackTensor0SNormedSpace (s : ℕ) (x : M) :
    NormedSpace Real (Tensor0SSpace s I x) :=
  Tensor0SBundle.tensor0SSpace_normedSpace s x

private local instance pullbackTensor0SAddCommGroup (s : ℕ) (x : M) :
    AddCommGroup (Tensor0SSpace s I x) :=
  @NormedAddCommGroup.toAddCommGroup _
    (pullbackTensor0SNormedAddCommGroup (I := I) s x)

private local instance pullbackTensor0SModule (s : ℕ) (x : M) :
    Module Real (Tensor0SSpace s I x) :=
  @NormedSpace.toModule _ _ _ _ (pullbackTensor0SNormedSpace (I := I) s x)

private local instance pullbackTensor0STopologicalSpace (s : ℕ) (x : M) :
    TopologicalSpace (Tensor0SSpace s I x) :=
  @UniformSpace.toTopologicalSpace _
    (@PseudoMetricSpace.toUniformSpace _
      (@MetricSpace.toPseudoMetricSpace _
        (@NormedAddCommGroup.toMetricSpace _
          (pullbackTensor0SNormedAddCommGroup (I := I) s x))))

noncomputable def tensor0SEvalCLM {s : ℕ} {x : M}
    (v : Fin s → TangentSpace I x) :
    Tensor0SSpace s I x →L[Real] Real :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A ↦ A v
    map_add' := by
      intro A B
      rfl
    map_smul' := by
      intro c A
      rfl }

@[simp]
theorem tensor0SEvalCLM_apply {s : ℕ} {x : M}
    (v : Fin s → TangentSpace I x) (A : Tensor0SSpace s I x) :
    tensor0SEvalCLM (I := I) (M := M) v A = A v :=
  rfl

private noncomputable def tensor0SPullbackValue {s : ℕ} {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace s I y) : Tensor0SSpace s I x :=
  Tensor0SSpace.ofModel (I := I) (x := x)
    ((Tensor0SSpace.toModel A).compContinuousLinearMap
      (fun _ : Fin s ↦ LinearMap.toContinuousLinearMap e.toLinearMap))

private theorem tensor0SPullbackValue_apply {s : ℕ} {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace s I y) (v : Fin s → TangentSpace I x) :
    tensor0SPullbackValue (I := I) (M := M) e A v = A (fun i ↦ e (v i)) := by
  change
    ((Tensor0SSpace.toModel A).compContinuousLinearMap
      (fun _ : Fin s ↦ LinearMap.toContinuousLinearMap e.toLinearMap)) v = _
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

noncomputable def tensor0SPullbackCLM (s : ℕ) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    Tensor0SSpace s I y →L[Real] Tensor0SSpace s I x :=
  LinearMap.toContinuousLinearMap {
    toFun := tensor0SPullbackValue (I := I) (M := M) e
    map_add' := by
      intro A B
      apply tensor0SSpace_ext s x
      intro v
      simp only [tensor0SPullbackValue_apply, Tensor0SSpace.add_apply]
    map_smul' := by
      intro c A
      apply tensor0SSpace_ext s x
      intro v
      simp only [tensor0SPullbackValue_apply, Tensor0SSpace.smul_apply,
        RingHom.id_apply] }

@[simp]
theorem tensor0SPullbackCLM_apply (s : ℕ) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace s I y) (v : Fin s → TangentSpace I x) :
    tensor0SPullbackCLM (I := I) (M := M) s e A v = A (fun i ↦ e (v i)) :=
  tensor0SPullbackValue_apply (I := I) (M := M) e A v

noncomputable def tensor0SPullbackCLE (s : ℕ) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    Tensor0SSpace s I y ≃L[Real] Tensor0SSpace s I x where
  toFun := tensor0SPullbackCLM (I := I) (M := M) s e
  invFun := tensor0SPullbackCLM (I := I) (M := M) s e.symm
  left_inv A := by
    apply tensor0SSpace_ext s y
    intro v
    simp
  right_inv A := by
    apply tensor0SSpace_ext s x
    intro v
    simp
  map_add' A B := (tensor0SPullbackCLM (I := I) (M := M) s e).map_add A B
  map_smul' c A := (tensor0SPullbackCLM (I := I) (M := M) s e).map_smul c A
  continuous_toFun := (tensor0SPullbackCLM (I := I) (M := M) s e).continuous
  continuous_invFun := (tensor0SPullbackCLM (I := I) (M := M) s e.symm).continuous

@[simp]
theorem tensor0SPullbackCLE_apply (s : ℕ) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace s I y) :
    tensor0SPullbackCLE (I := I) (M := M) s e A =
      tensor0SPullbackCLM (I := I) (M := M) s e A :=
  rfl

@[simp]
theorem tensor0SPullbackCLE_symm_apply (s : ℕ) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace s I x) :
    (tensor0SPullbackCLE (I := I) (M := M) s e).symm A =
      tensor0SPullbackCLM (I := I) (M := M) s e.symm A :=
  rfl

end DifferentialGeometry
