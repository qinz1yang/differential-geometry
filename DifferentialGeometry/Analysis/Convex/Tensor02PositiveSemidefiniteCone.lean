import DifferentialGeometry.Analysis.Convex.ProperConeFace
import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.ContinuousEvaluation
import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.Nullspace

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

private local instance coneTensor02NormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  Tensor0SBundle.tensor0SSpace_normedAddCommGroup 2 x

private local instance coneTensor02NormedSpace (x : M) :
    NormedSpace Real
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  Tensor0SBundle.tensor0SSpace_normedSpace 2 x

private local instance coneTensor02AddCommGroup (x : M) :
    AddCommGroup
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  @NormedAddCommGroup.toAddCommGroup _ (coneTensor02NormedAddCommGroup (I := I) x)

private local instance coneTensor02Module (x : M) :
    Module Real
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  @NormedSpace.toModule _ _ _ _ (coneTensor02NormedSpace (I := I) x)

private local instance coneTensor02TopologicalSpace (x : M) :
    TopologicalSpace
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  @UniformSpace.toTopologicalSpace _
    (@PseudoMetricSpace.toUniformSpace _
      (@MetricSpace.toPseudoMetricSpace _
        (@NormedAddCommGroup.toMetricSpace _
          (coneTensor02NormedAddCommGroup (I := I) x))))

noncomputable def tensor02SymmetricCone {x : M} :
    ProperCone Real
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  ⨅ v : TangentSpace I x, ⨅ w : TangentSpace I x,
    (⊥ : ProperCone Real Real).comap
      (tensor02EvalCLM (I := I) (M := M) v w -
        tensor02EvalCLM (I := I) (M := M) w v)

@[simp]
theorem mem_tensor02SymmetricCone {x : M}
    {A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x} :
    A ∈ tensor02SymmetricCone (I := I) (M := M) ↔
      ∀ v w : TangentSpace I x,
        eval02 (I := I) (M := M) A v w = eval02 (I := I) (M := M) A w v := by
  simp [tensor02SymmetricCone, sub_eq_zero]

noncomputable def tensor02QuadraticNonnegativeCone {x : M} :
    ProperCone Real
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  ⨅ v : TangentSpace I x,
    (ProperCone.positive Real Real).comap (tensor02EvalSelfCLM (I := I) (M := M) v)

@[simp]
theorem mem_tensor02QuadraticNonnegativeCone {x : M}
    {A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x} :
    A ∈ tensor02QuadraticNonnegativeCone (I := I) (M := M) ↔
      ∀ v : TangentSpace I x, 0 ≤ quad02 (I := I) (M := M) A v := by
  simp [tensor02QuadraticNonnegativeCone]

noncomputable def tensor02PositiveSemidefiniteCone {x : M} :
    ProperCone Real
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  tensor02SymmetricCone (I := I) (M := M) ⊓
    tensor02QuadraticNonnegativeCone (I := I) (M := M)

@[simp]
theorem mem_tensor02PositiveSemidefiniteCone {x : M}
    {A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x} :
    A ∈ tensor02PositiveSemidefiniteCone (I := I) (M := M) ↔
      (∀ v w : TangentSpace I x,
        eval02 (I := I) (M := M) A v w = eval02 (I := I) (M := M) A w v) ∧
      ∀ v : TangentSpace I x, 0 ≤ quad02 (I := I) (M := M) A v := by
  simp [tensor02PositiveSemidefiniteCone]

theorem tensor02EvalSelfCLM_isDualElement {x : M} (v : TangentSpace I x) :
    ProperCone.IsDualElement
      (C := tensor02PositiveSemidefiniteCone (I := I) (M := M))
      (tensor02EvalSelfCLM (I := I) (M := M) v :
        StrongDual Real
          (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)) := by
  intro A hA
  exact (mem_tensor02PositiveSemidefiniteCone.mp hA).2 v

theorem mem_tensor02PositiveSemidefinite_dualZeroFace {x : M}
    {A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x}
    {v : TangentSpace I x} :
    A ∈ (tensor02PositiveSemidefiniteCone (I := I) (M := M)).dualZeroFace
        (tensor02EvalSelfCLM (I := I) (M := M) v :
          StrongDual Real
            (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)) ↔
      A ∈ tensor02PositiveSemidefiniteCone (I := I) (M := M) ∧
        v ∈ twoTensorLeftKernel (I := I) (M := M) A := by
  rw [ProperCone.mem_dualZeroFace]
  constructor
  · rintro ⟨hA, hv⟩
    refine ⟨hA, ?_⟩
    exact (quad02_eq_zero_iff_mem_twoTensorLeftKernel
      (I := I) (M := M) A
      (mem_tensor02PositiveSemidefiniteCone.mp hA).1
      (mem_tensor02PositiveSemidefiniteCone.mp hA).2).mp hv
  · rintro ⟨hA, hv⟩
    refine ⟨hA, ?_⟩
    exact (quad02_eq_zero_iff_mem_twoTensorLeftKernel
      (I := I) (M := M) A
      (mem_tensor02PositiveSemidefiniteCone.mp hA).1
      (mem_tensor02PositiveSemidefiniteCone.mp hA).2).mpr hv

theorem tensor02PullbackCLE_mem_positiveSemidefiniteCone_iff {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) (A : Tensor0SSpace 2 I y) :
    tensor02PullbackCLE (I := I) (M := M) e A ∈
        tensor02PositiveSemidefiniteCone (I := I) (M := M) ↔
      A ∈ tensor02PositiveSemidefiniteCone (I := I) (M := M) := by
  constructor
  · intro hA
    obtain ⟨hsym, hnonneg⟩ := mem_tensor02PositiveSemidefiniteCone.mp hA
    apply mem_tensor02PositiveSemidefiniteCone.mpr
    constructor
    · intro v w
      have h := hsym (e.symm v) (e.symm w)
      simpa using h
    · intro v
      have h := hnonneg (e.symm v)
      simpa using h
  · intro hA
    obtain ⟨hsym, hnonneg⟩ := mem_tensor02PositiveSemidefiniteCone.mp hA
    apply mem_tensor02PositiveSemidefiniteCone.mpr
    constructor
    · intro v w
      simpa using hsym (e v) (e w)
    · intro v
      simpa using hnonneg (e v)

theorem tensor02PositiveSemidefiniteCone_map_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    (tensor02PositiveSemidefiniteCone (I := I) (M := M) :
      ProperCone Real (Tensor0SSpace 2 I y)).map
        (tensor02PullbackCLE (I := I) (M := M) e).toContinuousLinearMap =
      (tensor02PositiveSemidefiniteCone (I := I) (M := M) :
        ProperCone Real (Tensor0SSpace 2 I x)) := by
  apply ProperCone.ext
  intro A
  rw [ProperCone.mem_map_continuousLinearEquiv_iff]
  simpa using tensor02PullbackCLE_mem_positiveSemidefiniteCone_iff
    (I := I) (M := M) e.symm A

theorem tensor02PositiveSemidefinite_dualZeroFace_map_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) (v : TangentSpace I x) :
    ((tensor02PositiveSemidefiniteCone (I := I) (M := M) :
      ProperCone Real (Tensor0SSpace 2 I y)).dualZeroFace
        (tensor02EvalSelfCLM (I := I) (M := M) (e v))).map
          (tensor02PullbackCLE (I := I) (M := M) e).toContinuousLinearMap =
      ((tensor02PositiveSemidefiniteCone (I := I) (M := M) :
        ProperCone Real (Tensor0SSpace 2 I x)).dualZeroFace
          (tensor02EvalSelfCLM (I := I) (M := M) v)) := by
  rw [ProperCone.dualZeroFace_map_continuousLinearEquiv]
  rw [tensor02PositiveSemidefiniteCone_map_pullback]
  congr 1
  apply ContinuousLinearMap.ext
  intro A
  simp

end DifferentialGeometry
