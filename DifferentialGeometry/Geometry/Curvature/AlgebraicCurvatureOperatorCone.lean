import DifferentialGeometry.Geometry.Curvature.AlgebraicSectionalCone

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Analysis.InnerProductSpace
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private local instance curvatureOperatorTensor04NormedAddCommGroup (x : M) :
    NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
  Tensor0SBundle.tensor0SSpace_normedAddCommGroup 4 x

private local instance curvatureOperatorTensor04NormedSpace (x : M) :
    NormedSpace Real (Tensor04At (I := I) (M := M) x) :=
  Tensor0SBundle.tensor0SSpace_normedSpace 4 x

private local instance curvatureOperatorTensor04AddCommGroup (x : M) :
    AddCommGroup (Tensor04At (I := I) (M := M) x) :=
  @NormedAddCommGroup.toAddCommGroup _
    (curvatureOperatorTensor04NormedAddCommGroup (I := I) x)

private local instance curvatureOperatorTensor04Module (x : M) :
    Module Real (Tensor04At (I := I) (M := M) x) :=
  @NormedSpace.toModule _ _ _ _
    (curvatureOperatorTensor04NormedSpace (I := I) x)

private local instance curvatureOperatorTensor04TopologicalSpace (x : M) :
    TopologicalSpace (Tensor04At (I := I) (M := M) x) :=
  @UniformSpace.toTopologicalSpace _
    (@PseudoMetricSpace.toUniformSpace _
      (@MetricSpace.toPseudoMetricSpace _
        (@NormedAddCommGroup.toMetricSpace _
          (curvatureOperatorTensor04NormedAddCommGroup (I := I) x))))

def algebraicCurvatureOperatorQuadraticEval {x : M} {n : Nat}
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (c : Fin n → Real)
    (v w : Fin n → TangentSpace I x) : Real :=
  ∑ i, ∑ j, c i * c j *
    tensor04StdAt (I := I) (M := M)
      (A : Tensor04At (I := I) (M := M) x) (v i) (w i) (w j) (v j)

noncomputable def algebraicCurvatureOperatorQuadraticEvalCLM {x : M} {n : Nat}
    (c : Fin n → Real)
    (v w : Fin n → TangentSpace I x) :
    StrongDual Real
      (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :=
  ∑ i, ∑ j, (c i * c j) •
    ((tensor0SEvalCLM (I := I) (M := M)
      (vec4 (I := I) (v i) (w i) (w j) (v j))).comp
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) x).subtypeL)

@[simp]
theorem algebraicCurvatureOperatorQuadraticEvalCLM_apply {x : M} {n : Nat}
    (c : Fin n → Real)
    (v w : Fin n → TangentSpace I x)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    algebraicCurvatureOperatorQuadraticEvalCLM
        (I := I) (M := M) c v w A =
      algebraicCurvatureOperatorQuadraticEval
        (I := I) (M := M) A c v w := by
  simp [algebraicCurvatureOperatorQuadraticEvalCLM,
    algebraicCurvatureOperatorQuadraticEval, tensor04StdAt]

noncomputable def algebraicCurvatureOperatorNonnegativeCone {x : M} :
    ProperCone Real
      (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :=
  ⨅ n : Nat, ⨅ c : Fin n → Real,
    ⨅ v : Fin n → TangentSpace I x, ⨅ w : Fin n → TangentSpace I x,
      (ProperCone.positive Real Real).comap
        (algebraicCurvatureOperatorQuadraticEvalCLM
          (I := I) (M := M) c v w)

@[simp]
theorem mem_algebraicCurvatureOperatorNonnegativeCone {x : M}
    {A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x} :
    A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) ↔
      ∀ (n : Nat) (c : Fin n → Real)
        (v w : Fin n → TangentSpace I x),
        0 ≤ algebraicCurvatureOperatorQuadraticEval
          (I := I) (M := M) A c v w := by
  simp [algebraicCurvatureOperatorNonnegativeCone]

theorem algebraicCurvatureOperatorQuadraticEvalCLM_isDualElement
    {x : M} {n : Nat}
    (c : Fin n → Real) (v w : Fin n → TangentSpace I x) :
    ProperCone.IsDualElement
      (C := algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
      (algebraicCurvatureOperatorQuadraticEvalCLM
        (I := I) (M := M) c v w) := by
  intro A hA
  rw [algebraicCurvatureOperatorQuadraticEvalCLM_apply]
  exact (mem_algebraicCurvatureOperatorNonnegativeCone.mp hA) n c v w

theorem mem_algebraicCurvatureOperatorNonnegative_dualZeroFace
    {x : M} {n : Nat}
    {A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x}
    {c : Fin n → Real} {v w : Fin n → TangentSpace I x} :
    A ∈ (algebraicCurvatureOperatorNonnegativeCone
        (I := I) (M := M)).dualZeroFace
          (algebraicCurvatureOperatorQuadraticEvalCLM
            (I := I) (M := M) c v w) ↔
      A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) ∧
        algebraicCurvatureOperatorQuadraticEval
          (I := I) (M := M) A c v w = 0 := by
  simp [ProperCone.mem_dualZeroFace]

omit [FiniteDimensional Real E] in
theorem algebraicCurvatureOperatorQuadraticEval_singleton {x : M}
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (v w : TangentSpace I x) :
    algebraicCurvatureOperatorQuadraticEval (I := I) (M := M) A
        (fun _ : Fin 1 => 1) (fun _ : Fin 1 => v) (fun _ : Fin 1 => w) =
      tensor04SectionalEval (I := I) (M := M)
        (A : Tensor04At (I := I) (M := M) x) v w := by
  simp only [algebraicCurvatureOperatorQuadraticEval, Fin.sum_univ_one,
    mul_one, one_mul, tensor04StdAt]
  unfold tensor04SectionalEval
  congr 1

theorem algebraicCurvatureOperatorNonnegativeCone_le_sectionalNonnegativeCone
    {x : M} :
    (algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) x)) ≤
      (algebraicSectionalNonnegativeCone (I := I) (M := M) :
        ProperCone Real
          (algebraicCurvatureTensorSubmodule (I := I) (M := M) x)) := by
  intro A hA
  apply mem_algebraicSectionalNonnegativeCone.mpr
  intro v w
  rw [← algebraicCurvatureOperatorQuadraticEval_singleton]
  exact mem_algebraicCurvatureOperatorNonnegativeCone.mp hA 1
    (fun _ => 1) (fun _ => v) (fun _ => w)

@[simp]
theorem algebraicCurvatureOperatorQuadraticEval_pullback {x y : M} {n : Nat}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) y)
    (c : Fin n → Real)
    (v w : Fin n → TangentSpace I x) :
    algebraicCurvatureOperatorQuadraticEval (I := I) (M := M)
        (algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A) c v w =
      algebraicCurvatureOperatorQuadraticEval (I := I) (M := M) A c
        (fun i => e (v i)) (fun i => e (w i)) := by
  unfold algebraicCurvatureOperatorQuadraticEval
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [algebraicCurvatureTensorPullbackCLE_apply, tensor04StdAt_pullback]

theorem algebraicCurvatureTensorPullbackCLE_mem_curvatureOperatorNonnegativeCone_iff
    {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) y) :
    algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) ↔
      A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
  constructor
  · intro hA
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have h := mem_algebraicCurvatureOperatorNonnegativeCone.mp hA n c
      (fun i => e.symm (v i)) (fun i => e.symm (w i))
    rw [algebraicCurvatureOperatorQuadraticEval_pullback] at h
    simpa using h
  · intro hA
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    rw [algebraicCurvatureOperatorQuadraticEval_pullback]
    exact mem_algebraicCurvatureOperatorNonnegativeCone.mp hA n c
      (fun i => e (v i)) (fun i => e (w i))

theorem algebraicCurvatureOperatorNonnegativeCone_map_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    (algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) y)).map
          (algebraicCurvatureTensorPullbackCLE
            (I := I) (M := M) e).toContinuousLinearMap =
      (algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :
        ProperCone Real
          (algebraicCurvatureTensorSubmodule (I := I) (M := M) x)) := by
  apply ProperCone.ext
  intro A
  rw [ProperCone.mem_map_continuousLinearEquiv_iff]
  simpa using
    algebraicCurvatureTensorPullbackCLE_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) (M := M) e.symm A

theorem algebraicCurvatureOperatorNonnegative_dualZeroFace_map_pullback
    {x y : M} {n : Nat}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (c : Fin n → Real) (v w : Fin n → TangentSpace I x) :
    ((algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) y)).dualZeroFace
          (algebraicCurvatureOperatorQuadraticEvalCLM
            (I := I) (M := M) c (fun i => e (v i)) (fun i => e (w i)))).map
              (algebraicCurvatureTensorPullbackCLE
                (I := I) (M := M) e).toContinuousLinearMap =
      ((algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :
        ProperCone Real
          (algebraicCurvatureTensorSubmodule (I := I) (M := M) x)).dualZeroFace
            (algebraicCurvatureOperatorQuadraticEvalCLM
              (I := I) (M := M) c v w)) := by
  rw [ProperCone.dualZeroFace_map_continuousLinearEquiv]
  rw [algebraicCurvatureOperatorNonnegativeCone_map_pullback]
  congr 1
  apply ContinuousLinearMap.ext
  intro A
  rw [ContinuousLinearMap.comp_apply,
    algebraicCurvatureOperatorQuadraticEvalCLM_apply,
    algebraicCurvatureOperatorQuadraticEvalCLM_apply,
    algebraicCurvatureTensorPullbackCLE_symm]
  change algebraicCurvatureOperatorQuadraticEval (I := I) (M := M)
      (algebraicCurvatureTensorPullbackCLE
        (I := I) (M := M) e.symm A) c
          (fun i => e (v i)) (fun i => e (w i)) = _
  rw [algebraicCurvatureOperatorQuadraticEval_pullback]
  simp

end DifferentialGeometry.Geometry.Curvature
