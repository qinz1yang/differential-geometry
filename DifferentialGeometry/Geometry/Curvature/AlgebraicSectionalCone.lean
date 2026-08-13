import DifferentialGeometry.Analysis.Convex.Tensor04SectionalNonnegativeCone
import DifferentialGeometry.Geometry.Curvature.AlgebraicTensor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle Tensor0SBundle
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Analysis.InnerProductSpace
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private local instance algebraicSectionalTensor04NormedAddCommGroup (x : M) :
    NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
  Tensor0SBundle.tensor0SSpace_normedAddCommGroup 4 x

private local instance algebraicSectionalTensor04NormedSpace (x : M) :
    NormedSpace Real (Tensor04At (I := I) (M := M) x) :=
  Tensor0SBundle.tensor0SSpace_normedSpace 4 x

private local instance algebraicSectionalTensor04AddCommGroup (x : M) :
    AddCommGroup (Tensor04At (I := I) (M := M) x) :=
  @NormedAddCommGroup.toAddCommGroup _
    (algebraicSectionalTensor04NormedAddCommGroup (I := I) x)

private local instance algebraicSectionalTensor04Module (x : M) :
    Module Real (Tensor04At (I := I) (M := M) x) :=
  @NormedSpace.toModule _ _ _ _
    (algebraicSectionalTensor04NormedSpace (I := I) x)

private local instance algebraicSectionalTensor04TopologicalSpace (x : M) :
    TopologicalSpace (Tensor04At (I := I) (M := M) x) :=
  @UniformSpace.toTopologicalSpace _
    (@PseudoMetricSpace.toUniformSpace _
      (@MetricSpace.toPseudoMetricSpace _
        (@NormedAddCommGroup.toMetricSpace _
          (algebraicSectionalTensor04NormedAddCommGroup (I := I) x))))

noncomputable def algebraicSectionalEvalCLM {x : M}
    (v w : TangentSpace I x) :
    StrongDual Real
      (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :=
  (tensor04SectionalEvalCLM (I := I) (M := M) v w).comp
    (algebraicCurvatureTensorSubmodule (I := I) (M := M) x).subtypeL

@[simp]
theorem algebraicSectionalEvalCLM_apply {x : M}
    (v w : TangentSpace I x)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    algebraicSectionalEvalCLM (I := I) (M := M) v w A =
      tensor04SectionalEval (I := I) (M := M)
        (A : Tensor04At (I := I) (M := M) x) v w :=
  rfl

noncomputable def algebraicSectionalNonnegativeCone {x : M} :
    ProperCone Real
      (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :=
  (tensor04SectionalNonnegativeCone (I := I) (M := M)).comap
    (algebraicCurvatureTensorSubmodule (I := I) (M := M) x).subtypeL

@[simp]
theorem mem_algebraicSectionalNonnegativeCone {x : M}
    {A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x} :
    A ∈ algebraicSectionalNonnegativeCone (I := I) (M := M) ↔
      ∀ v w : TangentSpace I x,
        0 ≤ tensor04SectionalEval (I := I) (M := M)
          (A : Tensor04At (I := I) (M := M) x) v w := by
  simp [algebraicSectionalNonnegativeCone]

theorem algebraicSectionalEvalCLM_isDualElement {x : M}
    (v w : TangentSpace I x) :
    ProperCone.IsDualElement
      (C := algebraicSectionalNonnegativeCone (I := I) (M := M))
      (algebraicSectionalEvalCLM (I := I) (M := M) v w) := by
  intro A hA
  exact (mem_algebraicSectionalNonnegativeCone.mp hA) v w

theorem mem_algebraicSectionalNonnegative_dualZeroFace {x : M}
    {A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x}
    {v w : TangentSpace I x} :
    A ∈ (algebraicSectionalNonnegativeCone (I := I) (M := M)).dualZeroFace
        (algebraicSectionalEvalCLM (I := I) (M := M) v w) ↔
      A ∈ algebraicSectionalNonnegativeCone (I := I) (M := M) ∧
        tensor04SectionalEval (I := I) (M := M)
          (A : Tensor04At (I := I) (M := M) x) v w = 0 := by
  simp [ProperCone.mem_dualZeroFace]

@[simp]
theorem algebraicSectionalEval_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) y)
    (v w : TangentSpace I x) :
    tensor04SectionalEval (I := I) (M := M)
        ((algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
          Tensor04At (I := I) (M := M) x) v w =
      tensor04SectionalEval (I := I) (M := M)
        (A : Tensor04At (I := I) (M := M) y) (e v) (e w) := by
  change tensor04SectionalEval (I := I) (M := M)
      (tensor0SPullbackCLE (I := I) (M := M) 4 e A) v w = _
  exact tensor04SectionalEval_pullback (I := I) (M := M) e A v w

theorem algebraicCurvatureTensorPullbackCLE_mem_sectionalNonnegativeCone_iff
    {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) y) :
    algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A ∈
        algebraicSectionalNonnegativeCone (I := I) (M := M) ↔
      A ∈ algebraicSectionalNonnegativeCone (I := I) (M := M) := by
  constructor
  · intro hA
    apply mem_algebraicSectionalNonnegativeCone.mpr
    intro v w
    have h := mem_algebraicSectionalNonnegativeCone.mp hA
      (e.symm v) (e.symm w)
    rw [algebraicSectionalEval_pullback] at h
    simpa using h
  · intro hA
    apply mem_algebraicSectionalNonnegativeCone.mpr
    intro v w
    rw [algebraicSectionalEval_pullback]
    exact mem_algebraicSectionalNonnegativeCone.mp hA (e v) (e w)

theorem algebraicSectionalNonnegativeCone_map_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    (algebraicSectionalNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) y)).map
          (algebraicCurvatureTensorPullbackCLE
            (I := I) (M := M) e).toContinuousLinearMap =
      (algebraicSectionalNonnegativeCone (I := I) (M := M) :
        ProperCone Real
          (algebraicCurvatureTensorSubmodule (I := I) (M := M) x)) := by
  apply ProperCone.ext
  intro A
  rw [ProperCone.mem_map_continuousLinearEquiv_iff]
  simpa using
    algebraicCurvatureTensorPullbackCLE_mem_sectionalNonnegativeCone_iff
      (I := I) (M := M) e.symm A

theorem algebraicSectionalNonnegative_dualZeroFace_map_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (v w : TangentSpace I x) :
    ((algebraicSectionalNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) y)).dualZeroFace
          (algebraicSectionalEvalCLM (I := I) (M := M) (e v) (e w))).map
            (algebraicCurvatureTensorPullbackCLE
              (I := I) (M := M) e).toContinuousLinearMap =
      ((algebraicSectionalNonnegativeCone (I := I) (M := M) :
        ProperCone Real
          (algebraicCurvatureTensorSubmodule (I := I) (M := M) x)).dualZeroFace
            (algebraicSectionalEvalCLM (I := I) (M := M) v w)) := by
  rw [ProperCone.dualZeroFace_map_continuousLinearEquiv]
  rw [algebraicSectionalNonnegativeCone_map_pullback]
  congr 1
  apply ContinuousLinearMap.ext
  intro A
  change tensor04SectionalEval (I := I) (M := M)
      (((algebraicCurvatureTensorPullbackCLE
        (I := I) (M := M) e).symm A :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) y) :
          Tensor04At (I := I) (M := M) y) (e v) (e w) =
    tensor04SectionalEval (I := I) (M := M)
      (A : Tensor04At (I := I) (M := M) x) v w
  change tensor04SectionalEval (I := I) (M := M)
      ((algebraicCurvatureTensorPullbackCLE
        (I := I) (M := M) e.symm A :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) y) :
          Tensor04At (I := I) (M := M) y) (e v) (e w) = _
  rw [algebraicSectionalEval_pullback]
  simp

end DifferentialGeometry.Geometry.Curvature
