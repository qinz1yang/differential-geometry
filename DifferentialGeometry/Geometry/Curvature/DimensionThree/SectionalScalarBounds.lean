import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Positivity
import DifferentialGeometry.Geometry.Curvature.TraceNormalizedOperator
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

private theorem sum_mul_self_eq_sum_sq_eigenvalues
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.IsHermitian) :
    ∑ i : Fin 3, ∑ j : Fin 3, A i j * A i j =
      ∑ i : Fin 3, hA.eigenvalues i ^ 2 := by
  classical
  let U : Matrix (Fin 3) (Fin 3) ℝ := hA.eigenvectorUnitary
  let D : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hU : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hspec : A = U * D * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [U, D]
  have hsymm (i j : Fin 3) : A j i = A i j := by
    have h := congrFun (congrFun hA j) i
    simpa [Matrix.conjTranspose_apply] using h.symm
  have htrace : Matrix.trace (A * A) = ∑ i : Fin 3, ∑ j : Fin 3, A i j * A i j := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hsymm i j]
  rw [← htrace]
  calc
    Matrix.trace (A * A) = Matrix.trace ((U * D * star U) * (U * D * star U)) := by
      rw [← hspec]
    _ = Matrix.trace (U * (D * D) * star U) := by
      congr 1
      simp only [mul_assoc]
      rw [← mul_assoc (star U) U, hU, one_mul]
    _ = Matrix.trace (D * D * (star U * U)) := by
      rw [mul_assoc, Matrix.trace_mul_comm, mul_assoc]
    _ = Matrix.trace (D * D) := by rw [hU, mul_one]
    _ = ∑ i : Fin 3, hA.eigenvalues i ^ 2 := by
      dsimp only [D]
      rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [sq]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem normSq0S_eq_four_mul_sum_sq_orderedSectionalCurvaturesAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt g x basis)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    normSq0S g x 4 (A : Tensor04At (I := I) (M := M) x) =
      4 * ∑ i : Fin 3, orderedSectionalCurvaturesAt x basis A i ^ 2 := by
  classical
  have hA := curvatureOperatorMatrixAt_isHermitian x basis A
  have hperm : ∑ i : Fin 3, hA.eigenvalues i ^ 2 =
      ∑ i : Fin 3, orderedSectionalCurvaturesAt x basis A i ^ 2 := by
    unfold orderedSectionalCurvaturesAt Matrix.IsHermitian.eigenvalues
    exact (Fintype.equivOfCardEq (Fintype.card_fin 3)).symm.sum_comp
      (fun j => hA.eigenvalues₀ j ^ 2)
  rw [normSq0S, inner0S_algebraic_eq_four_mul_operatorInner g x basis horth A A,
    sum_mul_self_eq_sum_sq_eigenvalues hA, hperm]

variable [T2Space M] [I.Boundaryless] [BoundarylessManifold I M]

/-- In dimension three, a sectional lower bound and a scalar upper bound control
the norm of the curvature tensor at the same point. -/
theorem sqrt_normSq0S_le_of_sectional_lower_scalar_upper
    (g : SmoothRiemannianMetric I M) (x : M) (hdim : Module.finrank ℝ E = 3)
    {k B : ℝ} (hk : 0 ≤ k) (hsec : SectionalBoundedBelowAt g x (-k))
    (hR : metricScalarAt g x ≤ B) :
    Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤
      2 * Real.sqrt 3 * (max B 0 / 2 + 2 * k) := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt g x
    (show Module.finrank ℝ (TangentSpace I x) = 3 from hdim)
  let A := metricAlgebraicCurvatureTensorAt g x
  have hoperator : curvatureOperatorLowerBoundAt g x A k := by
    intro n c v w
    obtain ⟨a, b, hgram, hvalue⟩ :=
      DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.three_bivector_quadratic_realized
        g x hdim A c v w
    have hab := hsec a b
    change -k * (g.inner x a a * g.inner x b b - g.inner x a b ^ 2) ≤
      tensor04StandardAt (I := I) (A : Tensor04At (I := I) (M := M) x) a b b a at hab
    rw [hgram, hvalue] at hab
    linarith
  have hmin := (curvatureOperatorLowerBoundAt_iff_neg_sectionalMin_le
    g basis horth).mp hoperator
  have hanti := orderedSectionalCurvaturesAt_antitone x basis A
  have hlower (i : Fin 3) : -k ≤ orderedSectionalCurvaturesAt x basis A i := by
    have hi := hanti (show i ≤ 2 by omega)
    linarith
  have htrace : metricScalarAt g x =
      2 * ∑ i : Fin 3, orderedSectionalCurvaturesAt x basis A i := by
    have h := trace_traceNormalizedCurvatureOperatorMatrixAt g x basis horth
    rw [traceNormalizedCurvatureOperatorMatrixAt, Matrix.trace_smul,
      curvatureOperatorMatrixAt_trace_eq_sum_orderedSectionalCurvaturesAt] at h
    exact h.symm
  rw [Fin.sum_univ_three] at htrace
  let U : ℝ := max B 0 / 2 + 2 * k
  have hB : 0 ≤ max B 0 := le_max_right _ _
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hscalar : metricScalarAt g x ≤ max B 0 := hR.trans (le_max_left _ _)
  have heigen (i : Fin 3) : |orderedSectionalCurvaturesAt x basis A i| ≤ U := by
    have hi := hanti (Fin.zero_le i)
    have hi0 := hlower i
    have h1 := hlower 1
    have h2 := hlower 2
    rw [abs_le]
    dsimp only [U]
    constructor <;> linarith
  have hsquare (i : Fin 3) : orderedSectionalCurvaturesAt x basis A i ^ 2 ≤ U ^ 2 := by
    have hi := heigen i
    nlinarith [sq_abs (orderedSectionalCurvaturesAt x basis A i),
      abs_nonneg (orderedSectionalCurvaturesAt x basis A i)]
  have hnorm : normSq0S g x 4 (metricRm04At g x) ≤ 12 * U ^ 2 := by
    change normSq0S g x 4 (A : Tensor04At (I := I) (M := M) x) ≤ _
    rw [normSq0S_eq_four_mul_sum_sq_orderedSectionalCurvaturesAt g x basis horth A,
      Fin.sum_univ_three]
    linarith [hsquare 0, hsquare 1, hsquare 2]
  have hthree : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hfactor : (12 : ℝ) * U ^ 2 = (2 * Real.sqrt 3 * U) ^ 2 := by
    nlinarith [hthree]
  calc
    Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤ Real.sqrt (12 * U ^ 2) :=
      Real.sqrt_le_sqrt hnorm
    _ = 2 * Real.sqrt 3 * U := by
      rw [hfactor]
      exact Real.sqrt_sq (by positivity)

end DifferentialGeometry.Geometry.Curvature.DimensionThree
