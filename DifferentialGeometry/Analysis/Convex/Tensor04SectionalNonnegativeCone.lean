import DifferentialGeometry.Analysis.Convex.ProperConeFace
import DifferentialGeometry.Tensor.RSTensor.Pullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry

open Bundle Tensor0SBundle
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Analysis.InnerProductSpace
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]

private local instance coneTensor04NormedAddCommGroup (x : M) :
    NormedAddCommGroup (Tensor0SSpace 4 I x) :=
  Tensor0SBundle.tensor0SSpace_normedAddCommGroup 4 x

private local instance coneTensor04NormedSpace (x : M) :
    NormedSpace Real (Tensor0SSpace 4 I x) :=
  Tensor0SBundle.tensor0SSpace_normedSpace 4 x

private local instance coneTensor04AddCommGroup (x : M) :
    AddCommGroup (Tensor0SSpace 4 I x) :=
  @NormedAddCommGroup.toAddCommGroup _
    (coneTensor04NormedAddCommGroup (I := I) x)

private local instance coneTensor04Module (x : M) :
    Module Real (Tensor0SSpace 4 I x) :=
  @NormedSpace.toModule _ _ _ _ (coneTensor04NormedSpace (I := I) x)

private local instance coneTensor04TopologicalSpace (x : M) :
    TopologicalSpace (Tensor0SSpace 4 I x) :=
  @UniformSpace.toTopologicalSpace _
    (@PseudoMetricSpace.toUniformSpace _
      (@MetricSpace.toPseudoMetricSpace _
        (@NormedAddCommGroup.toMetricSpace _
          (coneTensor04NormedAddCommGroup (I := I) x))))

def tensor04SectionalArgs {x : M} (v w : TangentSpace I x) :
    Fin 4 → TangentSpace I x :=
  fun i ↦ if i = 0 then v else if i = 1 then w else if i = 2 then w else v

def tensor04SectionalEval {x : M} (A : Tensor0SSpace 4 I x)
    (v w : TangentSpace I x) : Real :=
  A (tensor04SectionalArgs (I := I) v w)

noncomputable def tensor04SectionalEvalCLM {x : M}
    (v w : TangentSpace I x) : StrongDual Real (Tensor0SSpace 4 I x) :=
  tensor0SEvalCLM (I := I) (M := M) (tensor04SectionalArgs (I := I) v w)

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

@[simp]
theorem mem_tensor04SectionalNonnegativeCone {x : M}
    {A : Tensor0SSpace 4 I x} :
    A ∈ tensor04SectionalNonnegativeCone (I := I) (M := M) ↔
      ∀ v w : TangentSpace I x,
        0 ≤ tensor04SectionalEval (I := I) (M := M) A v w := by
  simp [tensor04SectionalNonnegativeCone]

theorem tensor04SectionalEvalCLM_isDualElement {x : M}
    (v w : TangentSpace I x) :
    ProperCone.IsDualElement
      (C := tensor04SectionalNonnegativeCone (I := I) (M := M))
      (tensor04SectionalEvalCLM (I := I) (M := M) v w) := by
  intro A hA
  exact (mem_tensor04SectionalNonnegativeCone.mp hA) v w

theorem mem_tensor04SectionalNonnegative_dualZeroFace {x : M}
    {A : Tensor0SSpace 4 I x} {v w : TangentSpace I x} :
    A ∈ (tensor04SectionalNonnegativeCone (I := I) (M := M)).dualZeroFace
        (tensor04SectionalEvalCLM (I := I) (M := M) v w) ↔
      A ∈ tensor04SectionalNonnegativeCone (I := I) (M := M) ∧
        tensor04SectionalEval (I := I) (M := M) A v w = 0 := by
  simp [ProperCone.mem_dualZeroFace]

@[simp]
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

theorem tensor0SPullbackCLE_mem_sectionalNonnegativeCone_iff {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace 4 I y) :
    tensor0SPullbackCLE (I := I) (M := M) 4 e A ∈
        tensor04SectionalNonnegativeCone (I := I) (M := M) ↔
      A ∈ tensor04SectionalNonnegativeCone (I := I) (M := M) := by
  constructor
  · intro hA
    apply mem_tensor04SectionalNonnegativeCone.mpr
    intro v w
    have h := mem_tensor04SectionalNonnegativeCone.mp hA (e.symm v) (e.symm w)
    rw [tensor04SectionalEval_pullback] at h
    simpa using h
  · intro hA
    apply mem_tensor04SectionalNonnegativeCone.mpr
    intro v w
    rw [tensor04SectionalEval_pullback]
    exact mem_tensor04SectionalNonnegativeCone.mp hA (e v) (e w)

theorem tensor04SectionalNonnegativeCone_map_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    (tensor04SectionalNonnegativeCone (I := I) (M := M) :
      ProperCone Real (Tensor0SSpace 4 I y)).map
        (tensor0SPullbackCLE (I := I) (M := M) 4 e).toContinuousLinearMap =
      (tensor04SectionalNonnegativeCone (I := I) (M := M) :
        ProperCone Real (Tensor0SSpace 4 I x)) := by
  apply ProperCone.ext
  intro A
  rw [ProperCone.mem_map_continuousLinearEquiv_iff]
  simpa using tensor0SPullbackCLE_mem_sectionalNonnegativeCone_iff
    (I := I) (M := M) e.symm A

theorem tensor04SectionalNonnegative_dualZeroFace_map_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (v w : TangentSpace I x) :
    ((tensor04SectionalNonnegativeCone (I := I) (M := M) :
      ProperCone Real (Tensor0SSpace 4 I y)).dualZeroFace
        (tensor04SectionalEvalCLM (I := I) (M := M) (e v) (e w))).map
          (tensor0SPullbackCLE (I := I) (M := M) 4 e).toContinuousLinearMap =
      ((tensor04SectionalNonnegativeCone (I := I) (M := M) :
        ProperCone Real (Tensor0SSpace 4 I x)).dualZeroFace
          (tensor04SectionalEvalCLM (I := I) (M := M) v w)) := by
  rw [ProperCone.dualZeroFace_map_continuousLinearEquiv]
  rw [tensor04SectionalNonnegativeCone_map_pullback]
  congr 1
  apply ContinuousLinearMap.ext
  intro A
  change tensor04SectionalEval (I := I) (M := M)
      ((tensor0SPullbackCLE (I := I) (M := M) 4 e).symm A) (e v) (e w) =
    tensor04SectionalEval (I := I) (M := M) A v w
  rw [tensor0SPullbackCLE_symm_apply]
  change tensor04SectionalEval (I := I) (M := M)
      (tensor0SPullbackCLE (I := I) (M := M) 4 e.symm A) (e v) (e w) = _
  rw [tensor04SectionalEval_pullback]
  simp

end DifferentialGeometry
