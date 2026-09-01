import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRank
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorLeastEigenvalue
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciReaction
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RankTrichotomy
import DifferentialGeometry.Geometry.Curvature.SectionalCone
import DifferentialGeometry.Geometry.Curvature.AlgebraicCurvatureOperatorConeMetric

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
theorem metricCurvatureOperatorRankAt_eq_zero_or_one_or_three_of_nonnegative_of_ricciReactionDefectAt_eq_zero
    (g : SmoothRiemannianMetric I M)
    (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hcone : metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hzero : ricciReactionDefectAt (I := I) g x = 0) :
    metricCurvatureOperatorRankAt (I := I) g x hdim = 0 ∨
      metricCurvatureOperatorRankAt (I := I) g x hdim = 1 ∨
      metricCurvatureOperatorRankAt (I := I) g x hdim = 3 := by
  obtain ⟨basis, l1, l2, l3, horth, h21, h32, hdiagRic⟩ :=
    ricciEigen3_ordered (I := I) (M := M) g
      (metricRicciAt (I := I) (M := M) g x) hdim (by
        intro U V
        let basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis
          (I := I) x
        let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
            DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
          fun i j =>
            DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent
              (I := I) g x i j (extChartAt I x x)
        have hinv : MetricInverseInBasisGen (I := I) (M := M) g x basis gInv := by
          simpa [basis, gInv] using
            (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
              (I := I) g x)
        have hcomp :
            ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
              metricRicciAt (I := I) (M := M) g x
                  (fun q : Fin 2 => if q = 0 then basis i else basis j) =
                metricRicciAt (I := I) (M := M) g x
                  (fun q : Fin 2 => if q = 0 then basis j else basis i) := by
          intro i j
          change metricRicciAt (I := I) (M := M) g x
              (vec2 (I := I) (basis i) (basis j)) =
            metricRicciAt (I := I) (M := M) g x
              (vec2 (I := I) (basis j) (basis i))
          exact metricRicciSymm (I := I) (M := M) g basis gInv hinv i j
        exact
          DifferentialGeometry.Tensor.Coordinates.tensor0S_two_symm_of_coordFrame
            (I := I) basis (metricRicciAt (I := I) (M := M) g x) hcomp U V)
  let lambda : Real := l1 + l2 - l3
  let mu : Real := l1 + l3 - l2
  let nu : Real := l2 + l3 - l1
  have hinv : MetricInverseInBasisGen (I := I) (M := M) g x basis delta3 :=
    orthonormal_invBasis3 (I := I) g basis horth
  have hcompRic (i j : Fin 3) :
      metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j)) =
        ricciDiag3 l1 l2 l3 i j := by
    simpa [ricciCompAt_apply] using hdiagRic.2 i j
  have hscalar : metricScalarAt (I := I) (M := M) g x =
      ricciEigenScalar3 l1 l2 l3 := by
    rw [metricScalarAt_def,
      DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_eq_sum_basis
        (I := I) g basis delta3 hinv]
    simp_rw [hcompRic]
    unfold ricciEigenScalar3 ricciDiag3 delta3
    simp [Fin.sum_univ_three]
  have hdiag : RicciDiagAt (I := I)
      (metricRicciAt (I := I) (M := M) g x)
      (metricScalarAt (I := I) (M := M) g x)
      ((lambda + mu) / 2) ((lambda + nu) / 2) ((mu + nu) / 2) basis := by
    constructor
    · calc
        metricScalarAt (I := I) (M := M) g x = ricciEigenScalar3 l1 l2 l3 := hscalar
        _ = ricciEigenScalar3 ((lambda + mu) / 2) ((lambda + nu) / 2)
            ((mu + nu) / 2) := by
          dsimp [lambda, mu, nu]
          unfold ricciEigenScalar3
          ring
    · intro i j
      have h := hcompRic i j
      fin_cases i <;> fin_cases j <;>
        convert h using 1 <;>
          simp [ricciDiag3, lambda, mu, nu] <;> ring
  have horder : nu ≤ mu ∧ mu ≤ lambda := by
    constructor <;> dsimp [lambda, mu, nu] <;> linarith
  have hsectionalCone : metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
      algebraicSectionalNonnegativeCone (I := I) (M := M) :=
    algebraicCurvatureOperatorNonnegativeCone_le_sectionalNonnegativeCone hcone
  have hsec :=
    (metricAlgebraicCurvatureTensorAt_mem_algebraicSectionalNonnegativeCone_iff
      (I := I) (M := M) g x).mp hsectionalCone
  have htrace := metricRiemannFromRicci3DTraceDataAt
    (I := I) (M := M) g x basis horth
  have hnegdiag : RicciDiagAt (I := I)
      (-metricRicciAt (I := I) (M := M) g x)
      (-metricScalarAt (I := I) (M := M) g x)
      (-((lambda + mu) / 2)) (-((lambda + nu) / 2))
      (-((mu + nu) / 2)) basis := by
    constructor
    · calc
        -metricScalarAt (I := I) (M := M) g x = -ricciEigenScalar3 l1 l2 l3 := by
          rw [hscalar]
        _ = ricciEigenScalar3 (-((lambda + mu) / 2)) (-((lambda + nu) / 2))
            (-((mu + nu) / 2)) := by
          dsimp [ricciEigenScalar3, lambda, mu, nu]
          ring
    · intro i j
      change -(ricciCompAt (I := I) basis
        (metricRicciAt (I := I) (M := M) g x) i j) = _
      rw [hdiag.2 i j]
      fin_cases i <;> fin_cases j <;>
        simp [ricciDiag3]
  have hcomp := stdRmComp_eq_diag (I := I) htrace hnegdiag
  have hlambda_nonneg : 0 ≤ lambda := by
    have hcurv := hsec (basis 0) (basis 1)
    have hformula : metricRm04StdAt (I := I) (M := M) g x
        (basis 0) (basis 1) (basis 1) (basis 0) = lambda / 2 := by
      rw [metricRm04StdAt_apply]
      change standardRmCompAt (I := I) basis
        (metricRm04At (I := I) (M := M) g x) 0 1 1 0 = lambda / 2
      rw [hcomp]
      simp [stdRmDiag3, ricciDiag3, ricciEigenScalar3, delta3]
      ring
    rw [hformula] at hcurv
    linarith
  have hmu_nonneg : 0 ≤ mu := by
    have hcurv := hsec (basis 0) (basis 2)
    have hformula : metricRm04StdAt (I := I) (M := M) g x
        (basis 0) (basis 2) (basis 2) (basis 0) = mu / 2 := by
      rw [metricRm04StdAt_apply]
      change standardRmCompAt (I := I) basis
        (metricRm04At (I := I) (M := M) g x) 0 2 2 0 = mu / 2
      rw [hcomp]
      simp [stdRmDiag3, ricciDiag3, ricciEigenScalar3, delta3]
      ring
    rw [hformula] at hcurv
    linarith
  have hnu_nonneg : 0 ≤ nu := by
    have hcurv := hsec (basis 1) (basis 2)
    have hformula : metricRm04StdAt (I := I) (M := M) g x
        (basis 1) (basis 2) (basis 2) (basis 1) = nu / 2 := by
      rw [metricRm04StdAt_apply]
      change standardRmCompAt (I := I) basis
        (metricRm04At (I := I) (M := M) g x) 1 2 2 1 = nu / 2
      rw [hcomp]
      simp [stdRmDiag3, ricciDiag3, ricciEigenScalar3, delta3]
      ring
    rw [hformula] at hcurv
    linarith
  have hreaction' : curvatureReactionSumSquares3 nu mu lambda = 0 := by
    have hdiagPerm : RicciDiagAt (I := I)
        (metricRicciAt (I := I) (M := M) g x)
        (metricScalarAt (I := I) (M := M) g x)
        ((mu + lambda) / 2) ((nu + lambda) / 2) ((nu + mu) / 2) basis := by
      simpa [add_comm] using hdiag
    rw [← curvatureReactionPolynomial3_eq_sum_squares]
    rw [← ricciReactionDefectAt_eq_curvatureReactionPolynomial3
      (I := I) (M := M) g x basis horth nu mu lambda hdiagPerm]
    exact hzero
  have hreaction : curvatureReactionSumSquares3 lambda mu nu = 0 := by
    unfold curvatureReactionSumSquares3 at hreaction' ⊢
    convert hreaction' using 1
    ring
  obtain hcases := curvatureReactionSumSquares3_ordered_rank_trichotomy
    lambda mu nu hnu_nonneg horder hreaction
  rcases hcases with hflat | hcyl | hsphere
  · left
    rw [metricCurvatureOperatorRankAt_eq_matrix_rank_of_orthonormal
      (I := I) (M := M) g x hdim basis horth]
    rw [metricCurvatureOperatorMatrixAt_eq_diagonal_of_ricciDiag
      (I := I) (M := M) g x basis horth
      ((lambda + mu) / 2) ((lambda + nu) / 2) ((mu + nu) / 2) hdiag]
    rcases hflat with ⟨hlambda0, hmu0, hnu0⟩
    simp [curvatureOperatorDiagonal3, sec12Ric3, sec13Ric3, sec23Ric3,
      lambda, mu, nu, hlambda0, hmu0, hnu0]
  · right; left
    rw [metricCurvatureOperatorRankAt_eq_matrix_rank_of_orthonormal
      (I := I) (M := M) g x hdim basis horth]
    rw [metricCurvatureOperatorMatrixAt_eq_diagonal_of_ricciDiag
      (I := I) (M := M) g x basis horth
      ((lambda + mu) / 2) ((lambda + nu) / 2) ((mu + nu) / 2) hdiag]
    rcases hcyl with ⟨hlambda, hmu0, hnu0⟩
    have hhalf : lambda / 2 ≠ 0 := by positivity
    simp [curvatureOperatorDiagonal3, sec12Ric3, sec13Ric3, sec23Ric3,
      Matrix.rank_diagonal, lambda, mu, nu, hmu0, hnu0, hhalf]
  · right; right
    rw [metricCurvatureOperatorRankAt_eq_matrix_rank_of_orthonormal
      (I := I) (M := M) g x hdim basis horth]
    rw [metricCurvatureOperatorMatrixAt_eq_diagonal_of_ricciDiag
      (I := I) (M := M) g x basis horth
      ((lambda + mu) / 2) ((lambda + nu) / 2) ((mu + nu) / 2) hdiag]
    rcases hsphere with ⟨hnu, h_lam_mu, h_mu_nu⟩
    have hhalf : nu / 2 ≠ 0 := by positivity
    simp [curvatureOperatorDiagonal3, sec12Ric3, sec13Ric3, sec23Ric3,
      Matrix.rank_diagonal, lambda, mu, nu, h_lam_mu, h_mu_nu, hhalf]

omit [SigmaCompactSpace M] in
theorem metricCurvatureOperatorRankAt_eq_zero_or_one_or_three_of_leastCurvatureOperatorEigenvalueAt_nonneg_of_ricciReactionDefectAt_eq_zero
    (g : SmoothRiemannianMetric I M)
    (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hleast : 0 ≤ leastCurvatureOperatorEigenvalueAt (I := I) g x
      (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x))
    (hzero : ricciReactionDefectAt (I := I) g x = 0) :
    metricCurvatureOperatorRankAt (I := I) g x hdim = 0 ∨
      metricCurvatureOperatorRankAt (I := I) g x hdim = 1 ∨
      metricCurvatureOperatorRankAt (I := I) g x hdim = 3 := by
  apply metricCurvatureOperatorRankAt_eq_zero_or_one_or_three_of_nonnegative_of_ricciReactionDefectAt_eq_zero
    (I := I) (M := M) g x hdim
      ((zero_le_leastCurvatureOperatorEigenvalueAt_iff_mem_curvatureOperatorNonnegativeCone
        (I := I) (x := x) g hdim).mp hleast) hzero

end DifferentialGeometry.Geometry.Curvature.DimensionThree
