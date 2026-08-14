import DifferentialGeometry.Geometry.Curvature.AlgebraicCurvatureOperatorCone
import DifferentialGeometry.Geometry.Curvature.AlgebraicTensorMetric
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RiemannFromRicci
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open Bundle Tensor0SBundle
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M]

def algebraicCurvatureIdentityQuadraticEval
    (g : SmoothRiemannianMetric I M) {x : M} {n : Nat}
    (c : Fin n → Real) (v w : Fin n → TangentSpace I x) : Real :=
  ∑ i, ∑ j, c i * c j *
    ((g.inner x (v i) (v j)) * (g.inner x (w i) (w j)) -
      (g.inner x (v i) (w j)) * (g.inner x (w i) (v j)))

def CurvatureOperatorLowerBoundAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) (K : Real) : Prop :=
  ∀ (n : Nat) (c : Fin n → Real) (v w : Fin n → TangentSpace I x),
    0 ≤ algebraicCurvatureOperatorQuadraticEval (I := I) (M := M) A c v w +
      K * algebraicCurvatureIdentityQuadraticEval (I := I) g c v w

noncomputable def leastCurvatureOperatorEigenvalueAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) : Real :=
  -sInf {K : Real | CurvatureOperatorLowerBoundAt (I := I) g x A K}

def bivectorIndex3 (i : Fin 3) : Fin 3 × Fin 3 :=
  if i = 0 then (0, 1) else if i = 1 then (0, 2) else (1, 2)

noncomputable def curvatureOperatorMatrixAt
    (x : M) (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    Matrix (Fin 3) (Fin 3) Real :=
  fun i j =>
    tensor04StdAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
      (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
      (basis (bivectorIndex3 j).2) (basis (bivectorIndex3 j).1)

omit [FiniteDimensional Real E] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] in
theorem curvatureOperatorMatrixAt_isHermitian
    (x : M) (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (curvatureOperatorMatrixAt (I := I) x basis A).IsHermitian := by
  unfold curvatureOperatorMatrixAt
  ext i j
  have hsym := mem_algebraicCurvatureTensorSubmodule_iff_symmetries.mp A.2
  have hpair :=
    tensor04StdAt_pair_swap_of_mem_algebraicCurvatureTensorSubmodule A.2
      (basis (bivectorIndex3 j).1) (basis (bivectorIndex3 j).2)
      (basis (bivectorIndex3 i).2) (basis (bivectorIndex3 i).1)
  have hfirst := hsym.1 (basis (bivectorIndex3 i).2) (basis (bivectorIndex3 i).1)
    (basis (bivectorIndex3 j).1) (basis (bivectorIndex3 j).2)
  have hlast := hsym.2.1 (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
    (basis (bivectorIndex3 j).1) (basis (bivectorIndex3 j).2)
  have hji : tensor04StdAt (I := I) (M := M) A.1
      (basis (bivectorIndex3 j).1) (basis (bivectorIndex3 j).2)
      (basis (bivectorIndex3 i).2) (basis (bivectorIndex3 i).1) =
    tensor04StdAt (I := I) (M := M) A.1
      (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
      (basis (bivectorIndex3 j).2) (basis (bivectorIndex3 j).1) := by
    rw [hpair]
    rw [hfirst]
    rw [hlast]
    ring
  simpa [hji]

omit [FiniteDimensional Real E] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] in
theorem curvatureOperatorMatrixAt_trace_eq_sectionalSum
    (x : M) (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    Matrix.trace (curvatureOperatorMatrixAt (I := I) x basis A) =
      ∑ i : Fin 3,
        tensor04StdAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
          (basis (bivectorIndex3 i).2) (basis (bivectorIndex3 i).1) := by
  unfold Matrix.trace curvatureOperatorMatrixAt
  simp [Matrix.diag]

omit [FiniteDimensional Real E] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] in
theorem curvatureOperatorMatrixAt_eigenvalues_trace_eq_sectionalSum
    (x : M) (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    ∑ i : Fin 3, (curvatureOperatorMatrixAt_isHermitian (I := I) x basis A).eigenvalues i =
      ∑ i : Fin 3,
        tensor04StdAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
          (basis (bivectorIndex3 i).2) (basis (bivectorIndex3 i).1) := by
  calc
    ∑ i : Fin 3, (curvatureOperatorMatrixAt_isHermitian (I := I) x basis A).eigenvalues i =
        Matrix.trace (curvatureOperatorMatrixAt (I := I) x basis A) := by
      exact (Matrix.IsHermitian.trace_eq_sum_eigenvalues
        (hA := curvatureOperatorMatrixAt_isHermitian (I := I) x basis A)).symm
    _ = ∑ i : Fin 3,
        tensor04StdAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
          (basis (bivectorIndex3 i).2) (basis (bivectorIndex3 i).1) := by
      rw [curvatureOperatorMatrixAt_trace_eq_sectionalSum]

noncomputable def orderedSectionalCurvaturesAt
    (x : M) (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) : Fin 3 → Real :=
  (curvatureOperatorMatrixAt_isHermitian (I := I) x basis A).eigenvalues₀

omit [FiniteDimensional Real E] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] in
theorem orderedSectionalCurvaturesAt_antitone
    (x : M) (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    Antitone (orderedSectionalCurvaturesAt (I := I) x basis A) :=
  (curvatureOperatorMatrixAt_isHermitian (I := I) x basis A).eigenvalues₀_antitone

omit [FiniteDimensional Real E] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] in
theorem orderedSectionalCurvaturesAt_two_le_one
    (x : M) (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    orderedSectionalCurvaturesAt (I := I) x basis A 2 ≤
      orderedSectionalCurvaturesAt (I := I) x basis A 1 :=
  (orderedSectionalCurvaturesAt_antitone (I := I) x basis A) (by decide : (1 : Fin 3) ≤ 2)

omit [FiniteDimensional Real E] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] in
theorem orderedSectionalCurvaturesAt_one_le_zero
    (x : M) (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    orderedSectionalCurvaturesAt (I := I) x basis A 1 ≤
      orderedSectionalCurvaturesAt (I := I) x basis A 0 :=
  (orderedSectionalCurvaturesAt_antitone (I := I) x basis A) (by decide : (0 : Fin 3) ≤ 1)

omit [FiniteDimensional Real E] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] in
theorem algebraicCurvatureOperatorQuadraticEval_eq_matrixQuad
    (x : M) (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (c : Fin 3 → Real) :
    algebraicCurvatureOperatorQuadraticEval (I := I) (M := M) A c
        (fun i => basis (bivectorIndex3 i).1) (fun i => basis (bivectorIndex3 i).2) =
      ∑ i : Fin 3, ∑ j : Fin 3, c i * c j *
        curvatureOperatorMatrixAt (I := I) x basis A i j := by
  unfold algebraicCurvatureOperatorQuadraticEval curvatureOperatorMatrixAt
  simp

omit [FiniteDimensional Real E] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] in
theorem bivectorBasisPairing_eq_delta
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis) (p q : Fin 3) :
    (g.inner x (basis (bivectorIndex3 p).1) (basis (bivectorIndex3 q).1)) *
        (g.inner x (basis (bivectorIndex3 p).2) (basis (bivectorIndex3 q).2)) -
      (g.inner x (basis (bivectorIndex3 p).1) (basis (bivectorIndex3 q).2)) *
        (g.inner x (basis (bivectorIndex3 p).2) (basis (bivectorIndex3 q).1)) =
      if p = q then (1 : Real) else 0 := by
  fin_cases p <;> fin_cases q <;>
    simp [bivectorIndex3, horth 0 0, horth 0 1, horth 0 2, horth 1 0, horth 1 1, horth 1 2,
      horth 2 0, horth 2 1, horth 2 2, delta3]

end DifferentialGeometry.Geometry.Curvature.DimensionThree
