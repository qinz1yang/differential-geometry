import DifferentialGeometry.Analysis.Convex.ProperConeFace
import DifferentialGeometry.Tensor.RSTensor.Functoriality.Pullback

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Analysis.InnerProductSpace
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]

def tensor04SectionalArgs {x : M} (v w : TangentSpace I x) :
    Fin 4 → TangentSpace I x :=
  fun i ↦ if i = 0 then v else if i = 1 then w else if i = 2 then w else v

def tensor04SectionalEval {x : M} (A : Tensor0SSpace 4 I x)
    (v w : TangentSpace I x) : Real :=
  A (tensor04SectionalArgs (I := I) v w)

noncomputable def tensor04SectionalEvalCLM {x : M}
    (v w : TangentSpace I x) : StrongDual Real (Tensor0SSpace 4 I x) :=
  {
    toFun := fun A ↦ tensor04SectionalEval (I := I) (M := M) A v w
    map_add' := by
      intro A B
      rfl
    map_smul' := by
      intro c A
      rfl
    cont := by
      exact (ContinuousMultilinearMap.apply Real
        (fun _ : Fin 4 ↦ TangentSpace I x) Real
        (tensor04SectionalArgs (I := I) v w)).continuous.comp
          (tensor0SSpaceFiberContinuousLinearEquiv
            (I := I) 4 x).continuous }

omit [FiniteDimensional Real E] in
@[simp]
theorem tensor04SectionalEvalCLM_apply {x : M}
    (v w : TangentSpace I x) (A : Tensor0SSpace 4 I x) :
    tensor04SectionalEvalCLM (I := I) (M := M) v w A =
      tensor04SectionalEval (I := I) (M := M) A v w :=
  rfl

noncomputable def tensor04SectionalNonnegativeCone {x : M} :
    ProperCone Real (Tensor0SSpace 4 I x) :=
  ⨅ v : TangentSpace I x, ⨅ w : TangentSpace I x,
    (ProperCone.positive Real Real).comap
      (tensor04SectionalEvalCLM (I := I) (M := M) v w)

omit [FiniteDimensional Real E] in
@[simp]
theorem mem_tensor04SectionalNonnegativeCone {x : M}
    {A : Tensor0SSpace 4 I x} :
    A ∈ tensor04SectionalNonnegativeCone (I := I) (M := M) ↔
      ∀ v w : TangentSpace I x,
        0 ≤ tensor04SectionalEval (I := I) (M := M) A v w := by
  simp [tensor04SectionalNonnegativeCone]

omit [FiniteDimensional Real E] in
theorem tensor04SectionalEvalCLM_isDualElement {x : M}
    (v w : TangentSpace I x) :
    ProperCone.IsDualElement
      (C := tensor04SectionalNonnegativeCone (I := I) (M := M))
      (tensor04SectionalEvalCLM (I := I) (M := M) v w) := by
  intro A hA
  exact (mem_tensor04SectionalNonnegativeCone.mp hA) v w

omit [FiniteDimensional Real E] in
theorem mem_tensor04SectionalNonnegative_dualZeroFace {x : M}
    {A : Tensor0SSpace 4 I x} {v w : TangentSpace I x} :
    A ∈ (tensor04SectionalNonnegativeCone (I := I) (M := M)).dualZeroFace
        (tensor04SectionalEvalCLM (I := I) (M := M) v w) ↔
      A ∈ tensor04SectionalNonnegativeCone (I := I) (M := M) ∧
        tensor04SectionalEval (I := I) (M := M) A v w = 0 := by
  simp [ProperCone.mem_dualZeroFace]

theorem tensor04SectionalEval_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace 4 I y) (v w : TangentSpace I x) :
    tensor04SectionalEval (I := I) (M := M)
        (tensor0SPullbackCLE (I := I) (M := M) 4 e A) v w =
      tensor04SectionalEval (I := I) (M := M) A (e v) (e w) := by
  unfold tensor04SectionalEval
  rw [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply]
  congr 1
  funext i
  fin_cases i <;> simp [tensor04SectionalArgs]

private noncomputable def tensor04SectionalPullbackValue {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace 4 I y) : Tensor0SSpace 4 I x :=
  tensor0SPullbackCLE (I := I) (M := M) 4 e A

private theorem tensor04SectionalPullbackValue_apply {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace 4 I y) (v : Fin 4 → TangentSpace I x) :
    tensor04SectionalPullbackValue (I := I) (M := M) e A v =
      A (fun i ↦ e (v i)) := by
  unfold tensor04SectionalPullbackValue
  rw [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply]

private noncomputable def tensor04SectionalPullbackCLM {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    Tensor0SSpace 4 I y →L[Real] Tensor0SSpace 4 I x where
  toFun := tensor04SectionalPullbackValue (I := I) (M := M) e
  map_add' A B := by
    apply tensor0SSpace_ext 4 x
    intro v
    change (A + B) (fun i ↦ e (v i)) =
      A (fun i ↦ e (v i)) + B (fun i ↦ e (v i))
    rfl
  map_smul' c A := by
    apply tensor0SSpace_ext 4 x
    intro v
    change (c • A) (fun i ↦ e (v i)) = c • A (fun i ↦ e (v i))
    rfl
  cont := by
    change Continuous (fun A : Tensor0SSpace 4 I y =>
      tensor0SPullbackCLE (I := I) (M := M) 4 e A)
    exact (tensor0SPullbackCLE (I := I) (M := M) 4 e).continuous_toFun

noncomputable def tensor04SectionalPullbackCLE {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    Tensor0SSpace 4 I y ≃L[Real] Tensor0SSpace 4 I x where
  toFun := tensor04SectionalPullbackCLM (I := I) (M := M) e
  invFun := tensor04SectionalPullbackCLM (I := I) (M := M) e.symm
  left_inv A := by
    apply tensor0SSpace_ext 4 y
    intro v
    change A (fun i ↦ e (e.symm (v i))) = A v
    congr 1
    funext i
    simp
  right_inv A := by
    apply tensor0SSpace_ext 4 x
    intro v
    change A (fun i ↦ e.symm (e (v i))) = A v
    congr 1
    funext i
    simp
  map_add' A B := (tensor04SectionalPullbackCLM (I := I) (M := M) e).map_add A B
  map_smul' c A := (tensor04SectionalPullbackCLM (I := I) (M := M) e).map_smul c A
  continuous_toFun := (tensor04SectionalPullbackCLM (I := I) (M := M) e).continuous
  continuous_invFun := (tensor04SectionalPullbackCLM (I := I) (M := M) e.symm).continuous

@[simp]
theorem tensor04SectionalPullbackCLE_apply {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace 4 I y) (v : Fin 4 → TangentSpace I x) :
    tensor04SectionalPullbackCLE (I := I) (M := M) e A v =
      A (fun i ↦ e (v i)) :=
  tensor04SectionalPullbackValue_apply (I := I) (M := M) e A v

theorem tensor04SectionalEval_normPullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace 4 I y) (v w : TangentSpace I x) :
    tensor04SectionalEval (I := I) (M := M)
        (tensor04SectionalPullbackCLE (I := I) (M := M) e A) v w =
      tensor04SectionalEval (I := I) (M := M) A (e v) (e w) := by
  unfold tensor04SectionalEval
  rw [tensor04SectionalPullbackCLE_apply]
  congr 1
  funext i
  fin_cases i <;> simp [tensor04SectionalArgs]

theorem tensor04SectionalPullbackCLE_mem_sectionalNonnegativeCone_iff {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace 4 I y) :
    tensor04SectionalPullbackCLE (I := I) (M := M) e A ∈
        tensor04SectionalNonnegativeCone (I := I) (M := M) ↔
      A ∈ tensor04SectionalNonnegativeCone (I := I) (M := M) := by
  constructor
  · intro hA
    apply mem_tensor04SectionalNonnegativeCone.mpr
    intro v w
    have h := mem_tensor04SectionalNonnegativeCone.mp hA (e.symm v) (e.symm w)
    rw [tensor04SectionalEval_normPullback] at h
    simpa using h
  · intro hA
    apply mem_tensor04SectionalNonnegativeCone.mpr
    intro v w
    rw [tensor04SectionalEval_normPullback]
    exact mem_tensor04SectionalNonnegativeCone.mp hA (e v) (e w)

theorem tensor04SectionalNonnegativeCone_map_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    (tensor04SectionalNonnegativeCone (I := I) (M := M) :
      ProperCone Real (Tensor0SSpace 4 I y)).map
        (tensor04SectionalPullbackCLE (I := I) (M := M) e).toContinuousLinearMap =
      (tensor04SectionalNonnegativeCone (I := I) (M := M) :
        ProperCone Real (Tensor0SSpace 4 I x)) := by
  apply ProperCone.ext
  intro A
  rw [ProperCone.mem_map_continuousLinearEquiv_iff]
  change tensor04SectionalPullbackCLE (I := I) (M := M) e.symm A ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M) ↔
    A ∈ tensor04SectionalNonnegativeCone (I := I) (M := M)
  exact tensor04SectionalPullbackCLE_mem_sectionalNonnegativeCone_iff
    (I := I) (M := M) e.symm A

theorem tensor04SectionalNonnegative_dualZeroFace_map_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (v w : TangentSpace I x) :
    ((tensor04SectionalNonnegativeCone (I := I) (M := M) :
      ProperCone Real (Tensor0SSpace 4 I y)).dualZeroFace
        (tensor04SectionalEvalCLM (I := I) (M := M) (e v) (e w))).map
          (tensor04SectionalPullbackCLE (I := I) (M := M) e).toContinuousLinearMap =
      ((tensor04SectionalNonnegativeCone (I := I) (M := M) :
        ProperCone Real (Tensor0SSpace 4 I x)).dualZeroFace
          (tensor04SectionalEvalCLM (I := I) (M := M) v w)) := by
  rw [ProperCone.dualZeroFace_map_continuousLinearEquiv]
  rw [tensor04SectionalNonnegativeCone_map_pullback]
  congr 1
  apply ContinuousLinearMap.ext
  intro A
  change tensor04SectionalEval (I := I) (M := M)
      ((tensor04SectionalPullbackCLE (I := I) (M := M) e).symm A) (e v) (e w) =
    tensor04SectionalEval (I := I) (M := M) A v w
  change tensor04SectionalEval (I := I) (M := M)
      (tensor04SectionalPullbackCLE (I := I) (M := M) e.symm A) (e v) (e w) = _
  rw [tensor04SectionalEval_normPullback]
  simp

end DifferentialGeometry
