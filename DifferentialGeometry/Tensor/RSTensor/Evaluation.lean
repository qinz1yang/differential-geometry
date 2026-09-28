import DifferentialGeometry.Tensor.RSTensor.Defs

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

section Quadratic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]

def quad02
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (v : TangentSpace I x) : Real :=
  A (fun _ : Fin 2 => v)

def eval02
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (v w : TangentSpace I x) : Real :=
  A (fun i : Fin 2 => if i = 0 then v else w)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
@[simp] theorem eval02_self
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (v : TangentSpace I x) :
    eval02 (I := I) (M := M) A v v = quad02 (I := I) (M := M) A v := by
  unfold eval02 quad02
  congr 1
  funext i
  by_cases hi : i = 0
  · simp [hi]
  · simp [hi]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem tensor02_smul2
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (a : Real) (v : TangentSpace I x) :
    quad02 (I := I) (M := M) A (a • v) =
      a * a * quad02 (I := I) (M := M) A v := by
  have hmap := A.map_smul_univ (fun _ : Fin 2 => a) (fun _ : Fin 2 => v)
  have hslots :
      (fun i : Fin 2 => (fun _ : Fin 2 => a) i • (fun _ : Fin 2 => v) i) =
        (fun _ : Fin 2 => a • v) := by
    funext i
    simp
  rw [hslots] at hmap
  simpa [quad02, Fin.prod_univ_two, pow_two, smul_eq_mul,
    mul_assoc, mul_comm, mul_left_comm] using hmap

end Quadratic

section ContinuousEvaluation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]

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

end ContinuousEvaluation

end DifferentialGeometry
