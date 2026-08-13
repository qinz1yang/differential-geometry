import DifferentialGeometry.Geometry.Curvature.AlgebraicForm
import DifferentialGeometry.Geometry.Curvature.Tensor
import DifferentialGeometry.Tensor.RSTensor.Pullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private local instance algebraicTensor04NormedAddCommGroup (x : M) :
    NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
  Tensor0SBundle.tensor0SSpace_normedAddCommGroup 4 x

private local instance algebraicTensor04NormedSpace (x : M) :
    NormedSpace Real (Tensor04At (I := I) (M := M) x) :=
  Tensor0SBundle.tensor0SSpace_normedSpace 4 x

private local instance algebraicTensor04AddCommGroup (x : M) :
    AddCommGroup (Tensor04At (I := I) (M := M) x) :=
  @NormedAddCommGroup.toAddCommGroup _
    (algebraicTensor04NormedAddCommGroup (I := I) x)

private local instance algebraicTensor04Module (x : M) :
    Module Real (Tensor04At (I := I) (M := M) x) :=
  @NormedSpace.toModule _ _ _ _ (algebraicTensor04NormedSpace (I := I) x)

private local instance algebraicTensor04TopologicalSpace (x : M) :
    TopologicalSpace (Tensor04At (I := I) (M := M) x) :=
  @UniformSpace.toTopologicalSpace _
    (@PseudoMetricSpace.toUniformSpace _
      (@MetricSpace.toPseudoMetricSpace _
        (@NormedAddCommGroup.toMetricSpace _
          (algebraicTensor04NormedAddCommGroup (I := I) x))))

omit [FiniteDimensional Real E] in
private theorem tensor04StdAt_add_left {x : M}
    (A : Tensor04At (I := I) (M := M) x)
    (x₁ x₂ y z w : TangentSpace I x) :
    tensor04StdAt (I := I) (M := M) A (x₁ + x₂) y z w =
      tensor04StdAt (I := I) (M := M) A x₁ y z w +
        tensor04StdAt (I := I) (M := M) A x₂ y z w := by
  have h := A.map_update_add (vec4 (I := I) 0 y z w) (0 : Fin 4) x₁ x₂
  have hupdate (v : TangentSpace I x) :
      Function.update (vec4 (I := I) 0 y z w) (0 : Fin 4) v =
        vec4 (I := I) v y z w := by
    funext i
    fin_cases i <;> simp [vec4]
  rw [hupdate (x₁ + x₂), hupdate x₁, hupdate x₂] at h
  exact h

omit [FiniteDimensional Real E] in
private theorem tensor04StdAt_smul_left {x : M}
    (A : Tensor04At (I := I) (M := M) x)
    (a : Real) (v y z w : TangentSpace I x) :
    tensor04StdAt (I := I) (M := M) A (a • v) y z w =
      a * tensor04StdAt (I := I) (M := M) A v y z w := by
  have h := A.map_update_smul (vec4 (I := I) 0 y z w) (0 : Fin 4) a v
  have hupdate (u : TangentSpace I x) :
      Function.update (vec4 (I := I) 0 y z w) (0 : Fin 4) u =
        vec4 (I := I) u y z w := by
    funext i
    fin_cases i <;> simp [vec4]
  rw [hupdate (a • v), hupdate v] at h
  simpa only [smul_eq_mul] using h

noncomputable def algebraicCurvatureTensorSubmodule (x : M) :
    Submodule Real (Tensor04At (I := I) (M := M) x) where
  carrier := {A | IsAlgCurvForm (tensor04StdAt (I := I) (M := M) A)}
  zero_mem' := by
    simpa only [tensor04StdAt, Tensor0SSpace.zero_apply] using
      (IsAlgCurvForm.zero (V := TangentSpace I x))
  add_mem' := by
    intro A B hA hB
    simpa only [tensor04StdAt, Tensor0SSpace.add_apply] using hA.add hB
  smul_mem' := by
    intro c A hA
    simpa only [tensor04StdAt, Tensor0SSpace.smul_apply, smul_eq_mul] using hA.smul c

omit [FiniteDimensional Real E] in
@[simp]
theorem mem_algebraicCurvatureTensorSubmodule {x : M}
    {A : Tensor04At (I := I) (M := M) x} :
    A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x ↔
      IsAlgCurvForm (tensor04StdAt (I := I) (M := M) A) :=
  Iff.rfl

omit [FiniteDimensional Real E] in
theorem mem_algebraicCurvatureTensorSubmodule_iff_symmetries {x : M}
    {A : Tensor04At (I := I) (M := M) x} :
    A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x ↔
      (∀ X Y Z W : TangentSpace I x,
        tensor04StdAt (I := I) (M := M) A X Y Z W =
          -tensor04StdAt (I := I) (M := M) A Y X Z W) ∧
      (∀ X Y Z W : TangentSpace I x,
        tensor04StdAt (I := I) (M := M) A X Y Z W =
          -tensor04StdAt (I := I) (M := M) A X Y W Z) ∧
      (∀ X Y Z W : TangentSpace I x,
        tensor04StdAt (I := I) (M := M) A X Y Z W +
          tensor04StdAt (I := I) (M := M) A Y Z X W +
          tensor04StdAt (I := I) (M := M) A Z X Y W = 0) := by
  constructor
  · intro hA
    have hForm := mem_algebraicCurvatureTensorSubmodule.mp hA
    exact ⟨hForm.anti_first, hForm.anti_last, hForm.bianchi⟩
  · rintro ⟨hFirst, hLast, hBianchi⟩
    apply mem_algebraicCurvatureTensorSubmodule.mpr
    exact
      { add_left := tensor04StdAt_add_left (I := I) (M := M) A
        smul_left := tensor04StdAt_smul_left (I := I) (M := M) A
        anti_first := hFirst
        anti_last := hLast
        bianchi := hBianchi }

omit [FiniteDimensional Real E] in
theorem tensor04StdAt_pair_swap_of_mem_algebraicCurvatureTensorSubmodule
    {x : M} {A : Tensor04At (I := I) (M := M) x}
    (hA : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (X Y Z W : TangentSpace I x) :
    tensor04StdAt (I := I) (M := M) A X Y Z W =
      tensor04StdAt (I := I) (M := M) A Z W X Y :=
  (mem_algebraicCurvatureTensorSubmodule.mp hA).pair_swap X Y Z W

@[simp]
theorem tensor04StdAt_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor04At (I := I) (M := M) y)
    (v₀ v₁ v₂ v₃ : TangentSpace I x) :
    tensor04StdAt (I := I) (M := M)
        (tensor0SPullbackCLE (I := I) (M := M) 4 e A) v₀ v₁ v₂ v₃ =
      tensor04StdAt (I := I) (M := M) A (e v₀) (e v₁) (e v₂) (e v₃) := by
  unfold tensor04StdAt
  rw [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply]
  congr 1
  funext i
  fin_cases i <;> simp [vec4]

theorem tensor0SPullbackCLE_mem_algebraicCurvatureTensorSubmodule_iff
    {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor04At (I := I) (M := M) y) :
    tensor0SPullbackCLE (I := I) (M := M) 4 e A ∈
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x ↔
      A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) y := by
  constructor
  · intro hA
    have hPull := mem_algebraicCurvatureTensorSubmodule.mp hA
    apply mem_algebraicCurvatureTensorSubmodule.mpr
    refine
      { add_left := ?_
        smul_left := ?_
        anti_first := ?_
        anti_last := ?_
        bianchi := ?_ }
    · intro x₁ x₂ z w q
      exact tensor04StdAt_add_left (I := I) (M := M) A x₁ x₂ z w q
    · intro a x z w q
      exact tensor04StdAt_smul_left (I := I) (M := M) A a x z w q
    · intro v₀ v₁ v₂ v₃
      have h := hPull.anti_first
        (e.symm v₀) (e.symm v₁) (e.symm v₂) (e.symm v₃)
      rw [tensor04StdAt_pullback, tensor04StdAt_pullback] at h
      simpa using h
    · intro v₀ v₁ v₂ v₃
      have h := hPull.anti_last
        (e.symm v₀) (e.symm v₁) (e.symm v₂) (e.symm v₃)
      rw [tensor04StdAt_pullback, tensor04StdAt_pullback] at h
      simpa using h
    · intro v₀ v₁ v₂ v₃
      have h := hPull.bianchi
        (e.symm v₀) (e.symm v₁) (e.symm v₂) (e.symm v₃)
      rw [tensor04StdAt_pullback, tensor04StdAt_pullback,
        tensor04StdAt_pullback] at h
      simpa using h
  · intro hA
    have hForm := mem_algebraicCurvatureTensorSubmodule.mp hA
    apply mem_algebraicCurvatureTensorSubmodule.mpr
    refine
      { add_left := ?_
        smul_left := ?_
        anti_first := ?_
        anti_last := ?_
        bianchi := ?_ }
    · intro x₁ x₂ z w q
      exact tensor04StdAt_add_left (I := I) (M := M)
        (tensor0SPullbackCLE (I := I) (M := M) 4 e A) x₁ x₂ z w q
    · intro a x z w q
      exact tensor04StdAt_smul_left (I := I) (M := M)
        (tensor0SPullbackCLE (I := I) (M := M) 4 e A) a x z w q
    · intro v₀ v₁ v₂ v₃
      rw [tensor04StdAt_pullback, tensor04StdAt_pullback]
      exact hForm.anti_first (e v₀) (e v₁) (e v₂) (e v₃)
    · intro v₀ v₁ v₂ v₃
      rw [tensor04StdAt_pullback, tensor04StdAt_pullback]
      exact hForm.anti_last (e v₀) (e v₁) (e v₂) (e v₃)
    · intro v₀ v₁ v₂ v₃
      rw [tensor04StdAt_pullback, tensor04StdAt_pullback,
        tensor04StdAt_pullback]
      exact hForm.bianchi (e v₀) (e v₁) (e v₂) (e v₃)

theorem algebraicCurvatureTensorSubmodule_map_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    (algebraicCurvatureTensorSubmodule (I := I) (M := M) y).map
        (tensor0SPullbackCLE (I := I) (M := M) 4 e).toLinearMap =
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
  apply Submodule.ext
  intro A
  rw [Submodule.mem_map_equiv]
  simpa using tensor0SPullbackCLE_mem_algebraicCurvatureTensorSubmodule_iff
    (I := I) (M := M) e.symm A

noncomputable def algebraicCurvatureTensorPullbackCLE {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    algebraicCurvatureTensorSubmodule (I := I) (M := M) y ≃L[Real]
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
  (tensor0SPullbackCLE (I := I) (M := M) 4 e).ofSubmodules
    (algebraicCurvatureTensorSubmodule (I := I) (M := M) y)
    (algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (algebraicCurvatureTensorSubmodule_map_pullback (I := I) (M := M) e)

@[simp]
theorem algebraicCurvatureTensorPullbackCLE_apply {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) y) :
    (algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A :
      Tensor04At (I := I) (M := M) x) =
        tensor0SPullbackCLE (I := I) (M := M) 4 e A :=
  rfl

@[simp]
theorem algebraicCurvatureTensorPullbackCLE_symm {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    (algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e).symm =
      algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e.symm := by
  apply ContinuousLinearEquiv.ext
  funext A
  apply Subtype.ext
  rfl

end DifferentialGeometry.Geometry.Curvature
