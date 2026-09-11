import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRank
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.LeastEigenvalue
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciReaction
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RankTrichotomy
import DifferentialGeometry.Geometry.Curvature.Metric.SectionalCone
import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open DifferentialGeometry.Tensor0SBundle

private theorem diagonal_fin_three_rank_one_cases (d : Fin 3 → Real)
    (h : (Matrix.diagonal d).rank = 1) :
    (d 0 ≠ 0 ∧ d 1 = 0 ∧ d 2 = 0) ∨
      (d 0 = 0 ∧ d 1 ≠ 0 ∧ d 2 = 0) ∨
      (d 0 = 0 ∧ d 1 = 0 ∧ d 2 ≠ 0) := by
  classical
  have hcard : Fintype.card {i : Fin 3 // d i ≠ 0} = 1 := by
    simpa only using (Matrix.rank_diagonal d).symm.trans h
  have hatMostOne {i j : Fin 3} (hij : i ≠ j) (hi : d i ≠ 0) (hj : d j ≠ 0) : False := by
    let e : Fin 2 → {k : Fin 3 // d k ≠ 0} := fun q =>
      if hq : q = 0 then ⟨i, hi⟩ else ⟨j, hj⟩
    have he : Function.Injective e := by
      intro q r hqr
      fin_cases q <;> fin_cases r <;> simp_all [e]
    have hle := Fintype.card_le_of_injective e he
    rw [hcard] at hle
    norm_num at hle
  by_cases h0 : d 0 = 0
  · by_cases h1 : d 1 = 0
    · by_cases h2 : d 2 = 0
      · have hzero : d = 0 := by
          funext i
          fin_cases i <;> simp_all
        rw [hzero] at h
        simp at h
      · exact Or.inr (Or.inr ⟨h0, h1, h2⟩)
    · by_cases h2 : d 2 = 0
      · exact Or.inr (Or.inl ⟨h0, h1, h2⟩)
      · exact False.elim (hatMostOne (i := 1) (j := 2) (by decide) h1 h2)
  · by_cases h1 : d 1 = 0
    · by_cases h2 : d 2 = 0
      · exact Or.inl ⟨h0, h1, h2⟩
      · exact False.elim (hatMostOne (i := 0) (j := 2) (by decide) h0 h2)
    · exact False.elim (hatMostOne (i := 0) (j := 1) (by decide) h0 h1)

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
        have hinv : MetricInverseInBasis (I := I) (M := M) g x basis gInv := by
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
  have hinv : MetricInverseInBasis (I := I) (M := M) g x basis delta3 :=
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
  have hcomp := standardRmComp_eq_diag (I := I) htrace hnegdiag
  have hlambda_nonneg : 0 ≤ lambda := by
    have hcurv := hsec (basis 0) (basis 1)
    have hformula : metricRm04StandardAt (I := I) (M := M) g x
        (basis 0) (basis 1) (basis 1) (basis 0) = lambda / 2 := by
      rw [metricRm04StandardAt_apply]
      change standardRmCompAt (I := I) basis
        (metricRm04At (I := I) (M := M) g x) 0 1 1 0 = lambda / 2
      rw [hcomp]
      simp [standardRmDiag3, ricciDiag3, ricciEigenScalar3, delta3]
      ring
    rw [hformula] at hcurv
    linarith
  have hmu_nonneg : 0 ≤ mu := by
    have hcurv := hsec (basis 0) (basis 2)
    have hformula : metricRm04StandardAt (I := I) (M := M) g x
        (basis 0) (basis 2) (basis 2) (basis 0) = mu / 2 := by
      rw [metricRm04StandardAt_apply]
      change standardRmCompAt (I := I) basis
        (metricRm04At (I := I) (M := M) g x) 0 2 2 0 = mu / 2
      rw [hcomp]
      simp [standardRmDiag3, ricciDiag3, ricciEigenScalar3, delta3]
      ring
    rw [hformula] at hcurv
    linarith
  have hnu_nonneg : 0 ≤ nu := by
    have hcurv := hsec (basis 1) (basis 2)
    have hformula : metricRm04StandardAt (I := I) (M := M) g x
        (basis 1) (basis 2) (basis 2) (basis 1) = nu / 2 := by
      rw [metricRm04StandardAt_apply]
      change standardRmCompAt (I := I) basis
        (metricRm04At (I := I) (M := M) g x) 1 2 2 1 = nu / 2
      rw [hcomp]
      simp [standardRmDiag3, ricciDiag3, ricciEigenScalar3, delta3]
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

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem two_mul_normSq0S_metricRicciAt_eq_metricScalarAt_sq_of_metricCurvatureOperatorRankAt_eq_one
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hrank : metricCurvatureOperatorRankAt (I := I) g x hdim = 1) :
    2 * normSq0S (I := I) g x 2
        (metricRicciAt (I := I) (M := M) g x) =
      metricScalarAt (I := I) (M := M) g x ^ 2 := by
  obtain ⟨basis, lambda, mu, nu, horth, hdiag⟩ :=
    exists_orthonormal_curvature_eigenframe (I := I) (M := M) g x hdim
  let d : Fin 3 → Real := fun i =>
    if i = 0 then nu / 2 else if i = 1 then mu / 2 else lambda / 2
  have hmatrix :
      curvatureOperatorDiagonal3 ((mu + nu) / 2) ((lambda + nu) / 2)
          ((lambda + mu) / 2) = Matrix.diagonal d := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [curvatureOperatorDiagonal3, d, sec12Ric3, sec13Ric3, sec23Ric3] <;>
      ring
  have hdrank : (Matrix.diagonal d).rank = 1 := by
    rw [← hmatrix]
    rw [← metricCurvatureOperatorMatrixAt_eq_diagonal_of_ricciDiag
      (I := I) (M := M) g x basis horth
      ((mu + nu) / 2) ((lambda + nu) / 2) ((lambda + mu) / 2) hdiag]
    rw [← metricCurvatureOperatorRankAt_eq_matrix_rank_of_orthonormal
      (I := I) (M := M) g x hdim basis horth]
    exact hrank
  have hcases := diagonal_fin_three_rank_one_cases d hdrank
  rw [normSq0S_metricRicciAt_eq_ricciEigenNormSq3_of_ricciDiag
    (I := I) (M := M) g x basis horth
      ((mu + nu) / 2) ((lambda + nu) / 2) ((lambda + mu) / 2) hdiag,
    hdiag.1]
  rcases hcases with hnu | hmu | hlambda
  · have hmu0 : mu = 0 := by simpa [d] using hnu.2.1
    have hlambda0 : lambda = 0 := by simpa [d] using hnu.2.2
    simp [ricciEigenNormSq3, ricciEigenScalar3, hmu0, hlambda0]
    ring
  · have hnu0 : nu = 0 := by simpa [d] using hmu.1
    have hlambda0 : lambda = 0 := by simpa [d] using hmu.2.2
    simp [ricciEigenNormSq3, ricciEigenScalar3, hnu0, hlambda0]
    ring
  · have hnu0 : nu = 0 := by simpa [d] using hlambda.1
    have hmu0 : mu = 0 := by simpa [d] using hlambda.2.1
    simp [ricciEigenNormSq3, ricciEigenScalar3, hnu0, hmu0]
    ring

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem exists_metricRicciAt_nullVector_of_metricCurvatureOperatorRankAt_eq_one
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hrank : metricCurvatureOperatorRankAt (I := I) g x hdim = 1) :
    ∃ v : TangentSpace I x, v ≠ 0 ∧
      metricRicciAt (I := I) (M := M) g x (vec2 (I := I) v v) = 0 := by
  obtain ⟨basis, lambda, mu, nu, horth, hdiag⟩ :=
    exists_orthonormal_curvature_eigenframe (I := I) (M := M) g x hdim
  let d : Fin 3 → Real := fun i =>
    if i = 0 then nu / 2 else if i = 1 then mu / 2 else lambda / 2
  have hmatrix :
      curvatureOperatorDiagonal3 ((mu + nu) / 2) ((lambda + nu) / 2)
          ((lambda + mu) / 2) = Matrix.diagonal d := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [curvatureOperatorDiagonal3, d, sec12Ric3, sec13Ric3, sec23Ric3] <;>
      ring
  have hdrank : (Matrix.diagonal d).rank = 1 := by
    rw [← hmatrix]
    rw [← metricCurvatureOperatorMatrixAt_eq_diagonal_of_ricciDiag
      (I := I) (M := M) g x basis horth
      ((mu + nu) / 2) ((lambda + nu) / 2) ((lambda + mu) / 2) hdiag]
    rw [← metricCurvatureOperatorRankAt_eq_matrix_rank_of_orthonormal
      (I := I) (M := M) g x hdim basis horth]
    exact hrank
  have hcases := diagonal_fin_three_rank_one_cases d hdrank
  rcases hcases with hnu | hmu | hlambda
  · refine ⟨basis 2, basis.ne_zero 2, ?_⟩
    have h := hdiag.2 2 2
    rw [ricciCompAt_apply] at h
    have hmu0 : mu = 0 := by simpa [d] using hnu.2.1
    have hlambda0 : lambda = 0 := by simpa [d] using hnu.2.2
    simpa [ricciDiag3, hmu0, hlambda0] using h
  · refine ⟨basis 1, basis.ne_zero 1, ?_⟩
    have h := hdiag.2 1 1
    rw [ricciCompAt_apply] at h
    have hnu0 : nu = 0 := by simpa [d] using hmu.1
    have hlambda0 : lambda = 0 := by simpa [d] using hmu.2.2
    simpa [ricciDiag3, hnu0, hlambda0] using h
  · refine ⟨basis 0, basis.ne_zero 0, ?_⟩
    have h := hdiag.2 0 0
    rw [ricciCompAt_apply] at h
    have hnu0 : nu = 0 := by simpa [d] using hlambda.1
    have hmu0 : mu = 0 := by simpa [d] using hlambda.2.1
    simpa [ricciDiag3, hnu0, hmu0] using h

end DifferentialGeometry.Geometry.Curvature.DimensionThree
