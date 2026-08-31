import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorBasis
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciReaction
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M]

def curvatureOperatorDiagonal3 (l₁ l₂ l₃ : Real) :
    Matrix (Fin 3) (Fin 3) Real :=
  Matrix.diagonal fun i =>
    if i = 0 then sec12Ric3 l₁ l₂ l₃
    else if i = 1 then sec13Ric3 l₁ l₂ l₃
    else sec23Ric3 l₁ l₂ l₃

omit [SigmaCompactSpace M] in
theorem metricCurvatureOperatorMatrixAt_eq_diagonal_of_ricciDiag
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (l₁ l₂ l₃ : Real)
    (hdiag : RicciDiagAt (I := I)
      (metricRicciAt (I := I) (M := M) g x)
      (metricScalarAt (I := I) (M := M) g x) l₁ l₂ l₃ basis) :
    curvatureOperatorMatrixAt (I := I) x basis
        (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x) =
      curvatureOperatorDiagonal3 l₁ l₂ l₃ := by
  let Ric := metricRicciAt (I := I) (M := M) g x
  let Rm := metricRm04At (I := I) (M := M) g x
  have htrace := DifferentialGeometry.Geometry.Curvature.metricRiemannFromRicci3DTraceDataAt
    (I := I) (M := M) g x basis horth
  have hnegdiag :
      RicciDiagAt (I := I) (-Ric)
        (-(metricScalarAt (I := I) (M := M) g x))
        (-l₁) (-l₂) (-l₃) basis := by
    rcases hdiag with ⟨hscalar, hric⟩
    constructor
    · unfold ricciEigenScalar3 at hscalar ⊢
      linarith
    · intro i j
      change -(ricciCompAt (I := I) basis Ric i j) =
        ricciDiag3 (-l₁) (-l₂) (-l₃) i j
      rw [hric i j]
      fin_cases i <;> fin_cases j <;> simp [ricciDiag3]
  have hcomp := stdRmComp_eq_diag (I := I) htrace hnegdiag
  ext i j
  change standardRmCompAt (I := I) basis Rm
      (bivectorIndex3 i).1 (bivectorIndex3 i).2
      (bivectorIndex3 j).2 (bivectorIndex3 j).1 = _
  rw [hcomp]
  fin_cases i <;> fin_cases j <;>
    simp [curvatureOperatorDiagonal3, bivectorIndex3, Matrix.diagonal,
      stdRmDiag3, ricciDiag3, ricciEigenScalar3, delta3,
      sec12Ric3, sec13Ric3, sec23Ric3] <;> ring

omit [CompleteSpace E] [IsManifold I 1 M]
    [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M] in
theorem curvatureOperatorMatrixAt_rank_eq_of_orthonormal
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis₁ basis₂ : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth₁ : OrthonormalBasisAt (I := I) g x basis₁)
    (horth₂ : OrthonormalBasisAt (I := I) g x basis₂)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (curvatureOperatorMatrixAt (I := I) x basis₁ A).rank =
      (curvatureOperatorMatrixAt (I := I) x basis₂ A).rank := by
  classical
  let O : Matrix (Fin 3) (Fin 3) Real :=
    bivectorFrameChangeMatrix (I := I) g basis₁ basis₂
  let R₁ : Matrix (Fin 3) (Fin 3) Real :=
    curvatureOperatorMatrixAt (I := I) x basis₁ A
  let R₂ : Matrix (Fin 3) (Fin 3) Real :=
    curvatureOperatorMatrixAt (I := I) x basis₂ A
  have hO : O * O.transpose = 1 := by
    simpa [O] using bivectorFrameChangeMatrix_mul_transpose_of_orthonormal
      (I := I) (M := M) g basis₁ basis₂ horth₁ horth₂
  have hconj : R₂ = O.transpose * R₁ * O := by
    simpa only [R₁, R₂,
      tensor04CurvatureOperatorMatrixAt_eq_curvatureOperatorMatrixAt] using
      tensor04CurvatureOperatorMatrixAt_conj_of_orthonormal
        (I := I) (M := M) g basis₁ basis₂ horth₁ A
  have hrecover : R₁ = O * R₂ * O.transpose := by
    rw [hconj]
    calc
      R₁ = 1 * R₁ * 1 := by simp
      _ = (O * O.transpose) * R₁ * (O * O.transpose) := by rw [hO]
      _ = O * (O.transpose * R₁ * O) * O.transpose := by
        noncomm_ring
  change R₁.rank = R₂.rank
  apply le_antisymm
  · rw [hrecover]
    exact (Matrix.rank_mul_le_left (O * R₂) O.transpose).trans
      (Matrix.rank_mul_le_right O R₂)
  · rw [hconj]
    exact (Matrix.rank_mul_le_left (O.transpose * R₁) O).trans
      (Matrix.rank_mul_le_right O.transpose R₁)

noncomputable def curvatureOperatorRankAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hdim : Module.finrank Real (TangentSpace I x) = 3) : Nat :=
  let basis := Classical.choose
    (DifferentialGeometry.Geometry.Curvature.exists_orthonormalBasisAt (I := I) g x hdim)
  (curvatureOperatorMatrixAt (I := I) x basis A).rank

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem curvatureOperatorRankAt_eq_matrix_rank_of_orthonormal
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis) :
    curvatureOperatorRankAt (I := I) g x A hdim =
      (curvatureOperatorMatrixAt (I := I) x basis A).rank := by
  unfold curvatureOperatorRankAt
  exact curvatureOperatorMatrixAt_rank_eq_of_orthonormal
    (I := I) (M := M) g x
      (Classical.choose
        (DifferentialGeometry.Geometry.Curvature.exists_orthonormalBasisAt
          (I := I) g x hdim)) basis
      (Classical.choose_spec
        (DifferentialGeometry.Geometry.Curvature.exists_orthonormalBasisAt
          (I := I) g x hdim)) horth A

noncomputable def metricCurvatureOperatorRankAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3) : Nat :=
  curvatureOperatorRankAt (I := I) g x
    (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x) hdim

omit [SigmaCompactSpace M] in
theorem metricCurvatureOperatorRankAt_eq_matrix_rank_of_orthonormal
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis) :
    metricCurvatureOperatorRankAt (I := I) g x hdim =
      (curvatureOperatorMatrixAt (I := I) x basis
        (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x)).rank :=
  curvatureOperatorRankAt_eq_matrix_rank_of_orthonormal
    (I := I) (M := M) g x
      (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x) hdim basis horth

end DifferentialGeometry.Geometry.Curvature.DimensionThree
