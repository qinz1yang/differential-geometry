import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.IteratedCovariantDerivativeFields
import DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian
import Mathlib.Topology.Algebra.MvPolynomial

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology BigOperators

abbrev CurvatureJetPolynomialVariable (n N : ℕ) :=
  (Fin n × Fin n) ⊕ (Σ j : Fin (N + 1), Fin (4 + j.val) → Fin n)

def polynomialCoefficientBound {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (C : σ → ℝ) : ℝ :=
  ∑ d ∈ P.support, |P.coeff d| * ∏ i : σ, C i ^ d i

theorem polynomialCoefficientBound_nonneg {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) {C : σ → ℝ} (hC : ∀ i, 0 ≤ C i) :
    0 ≤ polynomialCoefficientBound P C := by
  exact Finset.sum_nonneg fun d _ => mul_nonneg (abs_nonneg _)
    (Finset.prod_nonneg fun i _ => pow_nonneg (hC i) _)

theorem abs_polynomial_eval_le {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) {v C : σ → ℝ}
    (hv : ∀ i, |v i| ≤ C i) :
    |MvPolynomial.eval v P| ≤ polynomialCoefficientBound P C := by
  classical
  rw [MvPolynomial.eval_eq', polynomialCoefficientBound]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun d _ => ?_
  rw [abs_mul, Finset.abs_prod]
  simp only [abs_pow]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact Finset.prod_le_prod (fun i _ => pow_nonneg (abs_nonneg _) _)
    (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hv i) _)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance jetPolynomialC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
private local instance jetPolynomialC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

def tensorOfPolynomialComponents {n r : ℕ} {σ : Type*} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (P : (Fin r → Fin n) → MvPolynomial σ ℝ) (v : σ → ℝ) :
    Tensor0SSpace r I x :=
  (coordEquiv0S (I := I) basis r).symm (fun slots => MvPolynomial.eval v (P slots))

@[simp] theorem component0S_tensorOfPolynomialComponents
    {n r : ℕ} {σ : Type*} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (P : (Fin r → Fin n) → MvPolynomial σ ℝ) (v : σ → ℝ)
    (slots : Fin r → Fin n) :
    component0S (I := I) basis (tensorOfPolynomialComponents basis P v) slots =
      MvPolynomial.eval v (P slots) := by
  have h := congrFun ((coordEquiv0S (I := I) basis r).apply_symm_apply
    (fun slots => MvPolynomial.eval v (P slots))) slots
  simpa only [tensorOfPolynomialComponents, coordEquiv0S_apply] using h

theorem tensorOfPolynomialComponents_eq_of_components
    {n r : ℕ} {σ : Type*} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (P : (Fin r → Fin n) → MvPolynomial σ ℝ) (v : σ → ℝ)
    (A : Tensor0SSpace r I x)
    (hA : ∀ slots, component0S (I := I) basis A slots = MvPolynomial.eval v (P slots)) :
    tensorOfPolynomialComponents basis P v = A := by
  apply ext0S_basis basis
  intro slots
  rw [component0S_tensorOfPolynomialComponents, hA slots]

theorem tensor0S_continuousWithinAt_of_components
    {n r : ℕ} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    {A : ℝ → Tensor0SSpace r I x} {J : Set ℝ} {t : ℝ}
    (hA : ∀ slots, ContinuousWithinAt (fun s => component0S (I := I) basis (A s) slots) J t) :
    ContinuousWithinAt A J t := by
  have hsum : ContinuousWithinAt
      (fun s => ∑ slots, component0S (I := I) basis (A s) slots •
        tensor0SBasis (I := I) basis r slots) J t :=
    tendsto_finsetSum Finset.univ fun slots _ => (hA slots).smul tendsto_const_nhds
  simpa only [← tensor0SBasis_repr, Module.Basis.sum_repr] using hsum

theorem tensorOfPolynomialComponents_continuousWithinAt
    {n r : ℕ} {σ : Type*} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (P : (Fin r → Fin n) → MvPolynomial σ ℝ)
    {v : ℝ → σ → ℝ} {J : Set ℝ} {t : ℝ}
    (hv : ∀ i, ContinuousWithinAt (fun s => v s i) J t) :
    ContinuousWithinAt (fun s => tensorOfPolynomialComponents basis P (v s)) J t := by
  let L : ((Fin r → Fin n) → ℝ) →L[ℝ] Tensor0SSpace r I x :=
    (coordEquiv0S (I := I) basis r).symm.toLinearMap.toContinuousLinearMap
  have hvals : ContinuousWithinAt v J t := continuousWithinAt_pi.mpr hv
  have heval : ContinuousWithinAt
      (fun s slots => MvPolynomial.eval (v s) (P slots)) J t := by
    exact continuousWithinAt_pi.mpr fun slots =>
      (P slots).continuous_eval.continuousAt.comp_continuousWithinAt hvals
  exact L.continuous.continuousAt.comp_continuousWithinAt heval

section Flow

variable [CompleteSpace E] [T2Space M]

def curvatureJetPolynomialValues {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (N : ℕ) (t : ℝ) {n : ℕ} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) :
    CurvatureJetPolynomialVariable n N → ℝ
  | Sum.inl ij => basisInvMetric (I := I) (S.base.metric t) x basis ij.1 ij.2
  | Sum.inr js => component0S (I := I) basis (nablaKRm04Field S t js.1.val x) js.2

end Flow

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
