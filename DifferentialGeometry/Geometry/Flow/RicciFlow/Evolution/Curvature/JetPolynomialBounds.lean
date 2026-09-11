import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.JetPolynomials
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff BigOperators


def polynomialArrayBound {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℝ) (C : σ → ℝ) : ℝ :=
  ∑ i : ι, polynomialCoefficientBound (P i) C

theorem polynomialArrayBound_nonneg {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℝ) {C : σ → ℝ} (hC : ∀ i, 0 ≤ C i) :
    0 ≤ polynomialArrayBound P C :=
  Finset.sum_nonneg fun i _ => polynomialCoefficientBound_nonneg (P i) hC

theorem abs_polynomial_eval_le_arrayBound {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℝ) {v C : σ → ℝ}
    (hC : ∀ i, 0 ≤ C i) (hv : ∀ i, |v i| ≤ C i) (j : ι) :
    |MvPolynomial.eval v (P j)| ≤ polynomialArrayBound P C := by
  classical
  exact (abs_polynomial_eval_le (P j) hv).trans
    (Finset.single_le_sum (fun i _ => polynomialCoefficientBound_nonneg (P i) hC)
      (Finset.mem_univ j))


def curvatureJetVariableBound (n N : ℕ) (C : ℕ → ℝ) :
    CurvatureJetPolynomialVariable n N → ℝ
  | Sum.inl _ => 1
  | Sum.inr js => max 1 (C js.1.val)

theorem curvatureJetVariableBound_nonneg (n N : ℕ) (C : ℕ → ℝ)
    (i : CurvatureJetPolynomialVariable n N) :
    0 ≤ curvatureJetVariableBound n N C i := by
  cases i with
  | inl _ => exact zero_le_one
  | inr js => exact zero_le_one.trans (le_max_left _ _)


def curvatureJetPolynomialNormBound {n r N : ℕ}
    (P : (Fin r → Fin n) → MvPolynomial (CurvatureJetPolynomialVariable n N) ℝ)
    (C : ℕ → ℝ) : ℝ :=
  Real.sqrt ((n : ℝ) ^ r * (polynomialArrayBound P (curvatureJetVariableBound n N C)) ^ 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private local instance jetPolynomialBoundC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
private local instance jetPolynomialBoundC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


theorem norm_le_curvatureJetPolynomialNormBound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (t : ℝ) {x : M} {n r N : ℕ}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hON : ∀ i j, (S.base.metric t).inner x (basis i) (basis j) = if i = j then 1 else 0)
    (P : (Fin r → Fin n) → MvPolynomial (CurvatureJetPolynomialVariable n N) ℝ)
    (A : Tensor0SSpace r I x)
    (hP : ∀ slots, component0S (I := I) basis A slots =
      MvPolynomial.eval (curvatureJetPolynomialValues S N t basis) (P slots))
    (C : ℕ → ℝ)
    (hjet : ∀ j ≤ N, curvDerivNorm (I := I) j (S.base.metric t) x ≤ C j) :
    Real.sqrt (normSq0S (I := I) (S.base.metric t) x r A) ≤
      curvatureJetPolynomialNormBound P C := by
  classical
  have hinv : MetricInverseInBasis (I := I) (S.base.metric t) x basis
      (identityInvMetric (Idx := Fin n)) :=
    metricInverseInBasis_of_orthonormal (I := I) (S.base.metric t) basis hON
  have hinvEq : basisInvMetric (I := I) (S.base.metric t) x basis =
      identityInvMetric (Idx := Fin n) :=
    MetricInverseInBasis.unique (I := I) (S.base.metric t) x basis _ _
      (basisInvMetric_isInverse (I := I) (S.base.metric t) x basis) hinv
  have hv (i : CurvatureJetPolynomialVariable n N) :
      |curvatureJetPolynomialValues S N t basis i| ≤ curvatureJetVariableBound n N C i := by
    cases i with
    | inl ij =>
      change |basisInvMetric (I := I) (S.base.metric t) x basis ij.1 ij.2| ≤ 1
      rw [hinvEq]
      by_cases h : ij.1 = ij.2 <;> simp [identityInvMetric, diagonalInvMetric, h]
    | inr js =>
      have hcomp := abs_apply_le_norm0S (I := I) (S.base.metric t) x (4 + js.1.val)
        (nablaKRm04Field S t js.1.val x) (fun k => basis (js.2 k))
      have hn : Real.sqrt (normSq0S (I := I) (S.base.metric t) x (4 + js.1.val)
          (nablaKRm04Field S t js.1.val x)) =
          curvDerivNorm (I := I) js.1.val (S.base.metric t) x :=
        congrArg Real.sqrt (curvNormSq_eq (I := I) S js.1.val t x).symm
      have hc : |component0S (I := I) basis (nablaKRm04Field S t js.1.val x) js.2| ≤
          curvDerivNorm (I := I) js.1.val (S.base.metric t) x := by
        simpa only [component0S_apply, hON, ite_true, Real.sqrt_one,
          Finset.prod_const_one, mul_one, hn] using hcomp
      exact (hc.trans (hjet js.1.val (Nat.le_of_lt_succ js.1.isLt))).trans (le_max_right _ _)
  let W : ℝ := polynomialArrayBound P (curvatureJetVariableBound n N C)
  have hW : 0 ≤ W := polynomialArrayBound_nonneg P (curvatureJetVariableBound_nonneg n N C)
  have hcomp (slots : Fin r → Fin n) : |component0S (I := I) basis A slots| ≤ W := by
    rw [hP slots]
    exact abs_polynomial_eval_le_arrayBound P (curvatureJetVariableBound_nonneg n N C) hv slots
  have hnorm := Real.sqrt_le_sqrt
    (normSq0S_le_card_of_component_bound (I := I) (S.base.metric t) x r basis hinv A W hW hcomp)
  simpa only [curvatureJetPolynomialNormBound, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow, W] using hnorm

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
