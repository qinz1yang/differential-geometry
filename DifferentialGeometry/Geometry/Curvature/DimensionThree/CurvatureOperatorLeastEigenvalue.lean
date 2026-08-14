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

private theorem identityQuad_firstExpansion
    {n : Nat} (c : Fin n → Real) (r t : Fin n → Fin 3 → Real) :
    (∑ i : Fin n, ∑ j : Fin n, c i * c j *
      ((∑ p : Fin 3, r i p * r j p) * (∑ q : Fin 3, t i q * t j q))) =
      ∑ p : Fin 3, ∑ q : Fin 3,
        (∑ i : Fin n, c i * r i p * t i q) * (∑ j : Fin n, c j * r j p * t j q) := by
  have hexp : ∀ i j : Fin n, c i * c j *
      ((∑ p : Fin 3, r i p * r j p) * (∑ q : Fin 3, t i q * t j q)) =
      ∑ p : Fin 3, ∑ q : Fin 3, c i * c j * r i p * r j p * t i q * t j q := by
    intro i j
    rw [show (∑ p : Fin 3, r i p * r j p) * (∑ q : Fin 3, t i q * t j q) =
        ∑ p : Fin 3, (r i p * r j p) * (∑ q : Fin 3, t i q * t j q) from
      Finset.sum_mul Finset.univ (fun p => r i p * r j p) (∑ q : Fin 3, t i q * t j q)]
    simp_rw [show ∀ a : Real, a * (∑ q : Fin 3, t i q * t j q) =
        ∑ q : Fin 3, a * t i q * t j q from
      fun a => by
        rw [Finset.mul_sum Finset.univ (fun q => t i q * t j q) a]
        apply Finset.sum_congr rfl
        intro q _
        ring]
    rw [show c i * c j * (∑ p : Fin 3, ∑ q : Fin 3, r i p * r j p * t i q * t j q) =
        ∑ p : Fin 3, c i * c j * (∑ q : Fin 3, r i p * r j p * t i q * t j q) from
      Finset.mul_sum Finset.univ (fun p => ∑ q : Fin 3, r i p * r j p * t i q * t j q) (c i * c j)]
    simp_rw [show ∀ (p : Fin 3) (a : Real), a * (∑ q : Fin 3, r i p * r j p * t i q * t j q) =
        ∑ q : Fin 3, a * r i p * r j p * t i q * t j q from
      fun p a => by
        rw [Finset.mul_sum Finset.univ (fun q => r i p * r j p * t i q * t j q) a]
        apply Finset.sum_congr rfl
        intro q _
        ring]
  simp_rw [hexp]
  have h1 : (∑ i : Fin n, ∑ j : Fin n, ∑ p : Fin 3, ∑ q : Fin 3,
      c i * c j * r i p * r j p * t i q * t j q) =
      ∑ j : Fin n, ∑ i : Fin n, ∑ p : Fin 3, ∑ q : Fin 3,
        c i * c j * r i p * r j p * t i q * t j q := by
    simpa using (Finset.sum_comm (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin n)))
      (f := fun i j => ∑ p : Fin 3, ∑ q : Fin 3, c i * c j * r i p * r j p * t i q * t j q))
  have h2 : (∑ j : Fin n, ∑ i : Fin n, ∑ p : Fin 3, ∑ q : Fin 3,
      c i * c j * r i p * r j p * t i q * t j q) =
      ∑ j : Fin n, ∑ p : Fin 3, ∑ i : Fin n, ∑ q : Fin 3,
        c i * c j * r i p * r j p * t i q * t j q := by
    apply Finset.sum_congr rfl
    intro j _
    simpa using (Finset.sum_comm (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin 3)))
      (f := fun i p => ∑ q : Fin 3, c i * c j * r i p * r j p * t i q * t j q))
  have h3 : (∑ j : Fin n, ∑ p : Fin 3, ∑ i : Fin n, ∑ q : Fin 3,
      c i * c j * r i p * r j p * t i q * t j q) =
      ∑ j : Fin n, ∑ p : Fin 3, ∑ q : Fin 3, ∑ i : Fin n,
        c i * c j * r i p * r j p * t i q * t j q := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro p _
    simpa using (Finset.sum_comm (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin 3)))
      (f := fun i q => c i * c j * r i p * r j p * t i q * t j q))
  have h4 : (∑ j : Fin n, ∑ p : Fin 3, ∑ q : Fin 3, ∑ i : Fin n,
      c i * c j * r i p * r j p * t i q * t j q) =
      ∑ p : Fin 3, ∑ j : Fin n, ∑ q : Fin 3, ∑ i : Fin n,
        c i * c j * r i p * r j p * t i q * t j q := by
    simpa using (Finset.sum_comm (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin 3)))
      (f := fun j p => ∑ q : Fin 3, ∑ i : Fin n, c i * c j * r i p * r j p * t i q * t j q))
  have h5 : (∑ p : Fin 3, ∑ j : Fin n, ∑ q : Fin 3, ∑ i : Fin n,
      c i * c j * r i p * r j p * t i q * t j q) =
      ∑ p : Fin 3, ∑ q : Fin 3, ∑ j : Fin n, ∑ i : Fin n,
        c i * c j * r i p * r j p * t i q * t j q := by
    apply Finset.sum_congr rfl
    intro p _
    simpa using (Finset.sum_comm (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin 3)))
      (f := fun j q => ∑ i : Fin n, c i * c j * r i p * r j p * t i q * t j q))
  have h6 : (∑ p : Fin 3, ∑ q : Fin 3, ∑ j : Fin n, ∑ i : Fin n,
      c i * c j * r i p * r j p * t i q * t j q) =
      ∑ p : Fin 3, ∑ q : Fin 3, ∑ i : Fin n, ∑ j : Fin n,
        c i * c j * r i p * r j p * t i q * t j q := by
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    simpa using (Finset.sum_comm (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin n)))
      (f := fun j i => c i * c j * r i p * r j p * t i q * t j q))
  rw [h1, h2, h3, h4, h5, h6]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_mul_sum (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin n)))
    (f := fun i => c i * r i p * t i q) (g := fun j => c j * r j p * t j q)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem identityQuad_secondExpansion
    {n : Nat} (c : Fin n → Real) (r t : Fin n → Fin 3 → Real) :
    (∑ i : Fin n, ∑ j : Fin n, c i * c j *
      ((∑ p : Fin 3, r i p * t j p) * (∑ q : Fin 3, t i q * r j q))) =
      ∑ p : Fin 3, ∑ q : Fin 3,
        (∑ i : Fin n, c i * r i p * t i q) * (∑ j : Fin n, c j * r j q * t j p) := by
  have hexp : ∀ i j : Fin n, c i * c j *
      ((∑ p : Fin 3, r i p * t j p) * (∑ q : Fin 3, t i q * r j q)) =
      ∑ p : Fin 3, ∑ q : Fin 3, c i * c j * r i p * t j p * t i q * r j q := by
    intro i j
    rw [show (∑ p : Fin 3, r i p * t j p) * (∑ q : Fin 3, t i q * r j q) =
        ∑ p : Fin 3, (r i p * t j p) * (∑ q : Fin 3, t i q * r j q) from
      Finset.sum_mul Finset.univ (fun p => r i p * t j p) (∑ q : Fin 3, t i q * r j q)]
    simp_rw [show ∀ a : Real, a * (∑ q : Fin 3, t i q * r j q) =
        ∑ q : Fin 3, a * t i q * r j q from
      fun a => by
        rw [Finset.mul_sum Finset.univ (fun q => t i q * r j q) a]
        apply Finset.sum_congr rfl
        intro q _
        ring]
    rw [show c i * c j * (∑ p : Fin 3, ∑ q : Fin 3, r i p * t j p * t i q * r j q) =
        ∑ p : Fin 3, c i * c j * (∑ q : Fin 3, r i p * t j p * t i q * r j q) from
      Finset.mul_sum Finset.univ (fun p => ∑ q : Fin 3, r i p * t j p * t i q * r j q) (c i * c j)]
    simp_rw [show ∀ (p : Fin 3) (a : Real), a * (∑ q : Fin 3, r i p * t j p * t i q * r j q) =
        ∑ q : Fin 3, a * r i p * t j p * t i q * r j q from
      fun p a => by
        rw [Finset.mul_sum Finset.univ (fun q => r i p * t j p * t i q * r j q) a]
        apply Finset.sum_congr rfl
        intro q _
        ring]
  simp_rw [hexp]
  have h1 : (∑ i : Fin n, ∑ j : Fin n, ∑ p : Fin 3, ∑ q : Fin 3,
      c i * c j * r i p * t j p * t i q * r j q) =
      ∑ j : Fin n, ∑ i : Fin n, ∑ p : Fin 3, ∑ q : Fin 3,
        c i * c j * r i p * t j p * t i q * r j q := by
    simpa using (Finset.sum_comm (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin n)))
      (f := fun i j => ∑ p : Fin 3, ∑ q : Fin 3, c i * c j * r i p * t j p * t i q * r j q))
  have h2 : (∑ j : Fin n, ∑ i : Fin n, ∑ p : Fin 3, ∑ q : Fin 3,
      c i * c j * r i p * t j p * t i q * r j q) =
      ∑ j : Fin n, ∑ p : Fin 3, ∑ i : Fin n, ∑ q : Fin 3,
        c i * c j * r i p * t j p * t i q * r j q := by
    apply Finset.sum_congr rfl
    intro j _
    simpa using (Finset.sum_comm (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin 3)))
      (f := fun i p => ∑ q : Fin 3, c i * c j * r i p * t j p * t i q * r j q))
  have h3 : (∑ j : Fin n, ∑ p : Fin 3, ∑ i : Fin n, ∑ q : Fin 3,
      c i * c j * r i p * t j p * t i q * r j q) =
      ∑ j : Fin n, ∑ p : Fin 3, ∑ q : Fin 3, ∑ i : Fin n,
        c i * c j * r i p * t j p * t i q * r j q := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro p _
    simpa using (Finset.sum_comm (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin 3)))
      (f := fun i q => c i * c j * r i p * t j p * t i q * r j q))
  have h4 : (∑ j : Fin n, ∑ p : Fin 3, ∑ q : Fin 3, ∑ i : Fin n,
      c i * c j * r i p * t j p * t i q * r j q) =
      ∑ p : Fin 3, ∑ j : Fin n, ∑ q : Fin 3, ∑ i : Fin n,
        c i * c j * r i p * t j p * t i q * r j q := by
    simpa using (Finset.sum_comm (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin 3)))
      (f := fun j p => ∑ q : Fin 3, ∑ i : Fin n, c i * c j * r i p * t j p * t i q * r j q))
  have h5 : (∑ p : Fin 3, ∑ j : Fin n, ∑ q : Fin 3, ∑ i : Fin n,
      c i * c j * r i p * t j p * t i q * r j q) =
      ∑ p : Fin 3, ∑ q : Fin 3, ∑ j : Fin n, ∑ i : Fin n,
        c i * c j * r i p * t j p * t i q * r j q := by
    apply Finset.sum_congr rfl
    intro p _
    simpa using (Finset.sum_comm (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin 3)))
      (f := fun j q => ∑ i : Fin n, c i * c j * r i p * t j p * t i q * r j q))
  have h6 : (∑ p : Fin 3, ∑ q : Fin 3, ∑ j : Fin n, ∑ i : Fin n,
      c i * c j * r i p * t j p * t i q * r j q) =
      ∑ p : Fin 3, ∑ q : Fin 3, ∑ i : Fin n, ∑ j : Fin n,
        c i * c j * r i p * t j p * t i q * r j q := by
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    simpa using (Finset.sum_comm (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin n)))
      (f := fun j i => c i * c j * r i p * t j p * t i q * r j q))
  rw [h1, h2, h3, h4, h5, h6]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_mul_sum (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin n)))
    (f := fun i => c i * r i p * t i q) (g := fun j => c j * r j q * t j p)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem identityQuad_squareIdentity
    {n : Nat} (c : Fin n → Real) (r t : Fin n → Fin 3 → Real) :
    (∑ i : Fin n, ∑ j : Fin n, c i * c j *
      ((∑ p : Fin 3, r i p * r j p) * (∑ q : Fin 3, t i q * t j q) -
        (∑ p : Fin 3, r i p * t j p) * (∑ q : Fin 3, t i q * r j q))) =
      (1 / 2 : Real) * ∑ p : Fin 3, ∑ q : Fin 3,
        (∑ i : Fin n, c i * (r i p * t i q - r i q * t i p)) ^ 2 := by
  let A : Fin 3 → Fin 3 → Real := fun p q => ∑ i : Fin n, c i * r i p * t i q
  have hA_sub : ∀ p q : Fin 3,
      ∑ i : Fin n, c i * (r i p * t i q - r i q * t i p) = A p q - A q p := by
    intro p q
    dsimp [A]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    (∑ i : Fin n, ∑ j : Fin n, c i * c j *
      ((∑ p : Fin 3, r i p * r j p) * (∑ q : Fin 3, t i q * t j q) -
        (∑ p : Fin 3, r i p * t j p) * (∑ q : Fin 3, t i q * r j q))) =
        (∑ i : Fin n, ∑ j : Fin n, c i * c j *
          ((∑ p : Fin 3, r i p * r j p) * (∑ q : Fin 3, t i q * t j q))) -
        (∑ i : Fin n, ∑ j : Fin n, c i * c j *
          ((∑ p : Fin 3, r i p * t j p) * (∑ q : Fin 3, t i q * r j q))) := by
      have hsplit : (∑ i : Fin n, ∑ j : Fin n, c i * c j *
            ((∑ p : Fin 3, r i p * r j p) * (∑ q : Fin 3, t i q * t j q))) -
          (∑ i : Fin n, ∑ j : Fin n, c i * c j *
            ((∑ p : Fin 3, r i p * t j p) * (∑ q : Fin 3, t i q * r j q))) =
          ∑ i : Fin n, ∑ j : Fin n, (c i * c j *
            ((∑ p : Fin 3, r i p * r j p) * (∑ q : Fin 3, t i q * t j q)) - c i * c j *
            ((∑ p : Fin 3, r i p * t j p) * (∑ q : Fin 3, t i q * r j q))) := by
        calc
          (∑ i : Fin n, ∑ j : Fin n, c i * c j *
              ((∑ p : Fin 3, r i p * r j p) * (∑ q : Fin 3, t i q * t j q))) -
            (∑ i : Fin n, ∑ j : Fin n, c i * c j *
              ((∑ p : Fin 3, r i p * t j p) * (∑ q : Fin 3, t i q * r j q)))
              = ∑ i : Fin n, ((∑ j : Fin n, c i * c j *
                  ((∑ p : Fin 3, r i p * r j p) * (∑ q : Fin 3, t i q * t j q))) -
                ∑ j : Fin n, c i * c j *
                  ((∑ p : Fin 3, r i p * t j p) * (∑ q : Fin 3, t i q * r j q))) := by
                simp
          _ = ∑ i : Fin n, ∑ j : Fin n, (c i * c j *
              ((∑ p : Fin 3, r i p * r j p) * (∑ q : Fin 3, t i q * t j q)) - c i * c j *
              ((∑ p : Fin 3, r i p * t j p) * (∑ q : Fin 3, t i q * r j q))) := by
            apply Finset.sum_congr rfl
            intro i _
            simp
      rw [hsplit]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ p : Fin 3, ∑ q : Fin 3,
          (∑ i : Fin n, c i * r i p * t i q) * (∑ j : Fin n, c j * r j p * t j q)) -
        (∑ p : Fin 3, ∑ q : Fin 3,
          (∑ i : Fin n, c i * r i p * t i q) * (∑ j : Fin n, c j * r j q * t j p)) := by
      rw [identityQuad_firstExpansion c r t, identityQuad_secondExpansion c r t]
    _ = (1 / 2 : Real) * ∑ p : Fin 3, ∑ q : Fin 3, (A p q - A q p) ^ 2 := by
      dsimp [A]
      have hswap_sq :
          (∑ p : Fin 3, ∑ q : Fin 3, A q p * A q p) = ∑ p : Fin 3, ∑ q : Fin 3, A p q * A p q := by
        simpa using (Finset.sum_comm (s := (Finset.univ : Finset (Fin 3))) (t := (Finset.univ : Finset (Fin 3)))
          (f := fun q p => A q p * A q p)).symm
      have hswap_mixed :
          (∑ p : Fin 3, ∑ q : Fin 3, (A q p) * (A p q)) =
            ∑ p : Fin 3, ∑ q : Fin 3, (A p q) * (A q p) := by
        simpa using (Finset.sum_comm (s := (Finset.univ : Finset (Fin 3))) (t := (Finset.univ : Finset (Fin 3)))
          (f := fun q p => (A q p) * (A p q))).symm
      calc
        (∑ p : Fin 3, ∑ q : Fin 3, A p q * A p q) - ∑ p : Fin 3, ∑ q : Fin 3, A p q * A q p =
            (1 / 2 : Real) * ((∑ p : Fin 3, ∑ q : Fin 3, A p q * A p q) +
                (∑ p : Fin 3, ∑ q : Fin 3, A p q * A p q) -
                2 * ∑ p : Fin 3, ∑ q : Fin 3, A p q * A q p) := by
          ring
        _ = (1 / 2 : Real) * ((∑ p : Fin 3, ∑ q : Fin 3, A p q * A p q) +
              (∑ p : Fin 3, ∑ q : Fin 3, A q p * A q p) -
              2 * ∑ p : Fin 3, ∑ q : Fin 3, A p q * A q p) := by
          rw [hswap_sq]
        _ = (1 / 2 : Real) * ((∑ p : Fin 3, ∑ q : Fin 3, A p q * A p q) +
              (∑ p : Fin 3, ∑ q : Fin 3, A q p * A q p) -
              (∑ p : Fin 3, ∑ q : Fin 3, A p q * A q p) -
              (∑ p : Fin 3, ∑ q : Fin 3, A q p * A p q)) := by
          rw [hswap_mixed]
          ring
        _ = (1 / 2 : Real) * ∑ p : Fin 3, ∑ q : Fin 3, (A p q - A q p) ^ 2 := by
          congr 1
          have hbracket :
              (∑ p : Fin 3, ∑ q : Fin 3, A p q * A p q) +
                  (∑ p : Fin 3, ∑ q : Fin 3, A q p * A q p) -
                  (∑ p : Fin 3, ∑ q : Fin 3, A p q * A q p) -
                  (∑ p : Fin 3, ∑ q : Fin 3, A q p * A p q) =
                ∑ p : Fin 3, ∑ q : Fin 3,
                  (A p q * A p q + A q p * A q p - A p q * A q p - A q p * A p q) := by
            rw [← Finset.sum_add_distrib]
            rw [← Finset.sum_sub_distrib]
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro p _
            rw [← Finset.sum_add_distrib]
            rw [← Finset.sum_sub_distrib]
            rw [← Finset.sum_sub_distrib]
          rw [hbracket]
          apply Finset.sum_congr rfl
          intro p _
          apply Finset.sum_congr rfl
          intro q _
          ring
    _ = (1 / 2 : Real) * ∑ p : Fin 3, ∑ q : Fin 3,
        (∑ i : Fin n, c i * (r i p * t i q - r i q * t i p)) ^ 2 := by
      simp_rw [hA_sub]

omit [FiniteDimensional Real E] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] in
theorem algebraicCurvatureIdentityQuadraticEval_eq_sumSq
    (g : SmoothRiemannianMetric I M) (x : M) {n : Nat}
    (c : Fin n → Real) (v w : Fin n → TangentSpace I x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis) :
    algebraicCurvatureIdentityQuadraticEval (I := I) g c v w =
      (1 / 2 : Real) * ∑ p : Fin 3, ∑ q : Fin 3,
        (∑ i : Fin n, c i *
          (basis.repr (v i) p * basis.repr (w i) q -
            basis.repr (v i) q * basis.repr (w i) p)) ^ 2 := by
  unfold algebraicCurvatureIdentityQuadraticEval
  simp_rw [inner_eq_sum_repr3 (I := I) horth]
  exact identityQuad_squareIdentity c (fun i p => basis.repr (v i) p)
    (fun i q => basis.repr (w i) q)

omit [FiniteDimensional Real E] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] in
theorem algebraicCurvatureIdentityQuadraticEval_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) {n : Nat}
    (c : Fin n → Real) (v w : Fin n → TangentSpace I x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis) :
    0 ≤ algebraicCurvatureIdentityQuadraticEval (I := I) g c v w := by
  rw [algebraicCurvatureIdentityQuadraticEval_eq_sumSq (I := I) g x c v w basis horth]
  exact mul_nonneg (by norm_num : (0 : Real) ≤ 1 / 2)
    (Finset.sum_nonneg (by
      intro p _
      exact Finset.sum_nonneg (by
        intro q _
        exact sq_nonneg _)))

end DifferentialGeometry.Geometry.Curvature.DimensionThree
