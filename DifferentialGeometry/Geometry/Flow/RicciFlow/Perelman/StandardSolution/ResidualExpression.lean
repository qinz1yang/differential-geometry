import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CurvatureExpression
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CanonicalCurvatureEvolution

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.PDE.RicciFlow

def CurvatureExpression.sumFin {s : ℕ} : (n : ℕ) →
    (Fin n → CurvatureExpression s) → CurvatureExpression s
  | 0, _ => .zero s
  | n + 1, A => .add (A 0) (CurvatureExpression.sumFin n (fun q => A q.succ))

def CurvatureExpression.binaryContraction (k a b : ℕ)
    (e : Fin ((4 + a) + (4 + b)) ≃ Fin ((4 + k) + 4)) : CurvatureExpression (4 + k) :=
  .trace (.trace (.perm e (.product (.curvature a) (.curvature b))))

def CurvatureExpression.gamma (k : ℕ) : CurvatureExpression (4 + (k + 1)) :=
  .add (.add
    (.smul (-1) (sumFin (4 + k) (fun q => binaryContraction (k + 1) 1 k (sigmaRic1 k q))))
    (.smul (-1) (sumFin (4 + k) (fun q => binaryContraction (k + 1) 1 k (sigmaRic2 k q)))))
    (sumFin (4 + k) (fun q => binaryContraction (k + 1) 1 k (sigmaRic3 k q)))

def CurvatureExpression.comm (k : ℕ) : CurvatureExpression (4 + (k + 1)) :=
  .smul (-1) (.add (.add
    (sumFin (4 + k) (fun q => binaryContraction (k + 1) 1 k (sigmaDiffA k q)))
    (sumFin (4 + k) (fun q => binaryContraction (k + 1) 0 (k + 1) (sigmaDiffB k q))))
    (sumFin (4 + (k + 1)) (fun q =>
      if hq : q.val = 0 then binaryContraction (k + 1) (k + 1) 0 (sigmaCurv0 k)
      else binaryContraction (k + 1) (k + 1) 0 (sigmaCurvPos k q hq))))

def CurvatureExpression.residual : (k : ℕ) → CurvatureExpression (4 + k)
  | 0 => baseResidual
  | k + 1 => .add (.add (residual k).spatialDerivative (.smul (-1) (comm k)))
      (.smul (-1) (gamma k))

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem CurvatureExpression.eval_sumFin {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) {s : ℕ} (n : ℕ)
    (A : Fin n → CurvatureExpression s) :
    (sumFin n A).eval S t = ∑ q : Fin n, (A q).eval S t := by
  induction n with
  | zero => simp only [sumFin, eval, Fin.sum_univ_zero]
  | succ n ih =>
      change (A 0).eval S t + (sumFin n (fun q => A q.succ)).eval S t = _
      rw [ih, Fin.sum_univ_succ]

variable [CompleteSpace E]

theorem CurvatureExpression.eval_binaryContraction {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (k a b : ℕ)
    (e : Fin ((4 + a) + (4 + b)) ≃ Fin ((4 + k) + 4)) :
    (binaryContraction k a b e).eval S t = starBaseField S t k a b 0 e := by
  rfl

theorem CurvatureExpression.eval_gamma {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (k : ℕ) :
    (gamma k).eval S t = gammaStarField S t k := by
  simp only [gamma, eval, eval_sumFin, eval_binaryContraction, gammaStarField]

theorem CurvatureExpression.eval_comm {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : RealTimeInterval.RegularTime D) (k : ℕ) :
    (comm k).eval S (t : ℝ) = commStarField S t k := by
  simp only [comm, eval, eval_sumFin, eval_binaryContraction, commStarField]
  congr 2
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q.val = 0
  · simp only [dif_pos hq, eval_binaryContraction]
  · simp only [dif_neg hq, eval_binaryContraction]

theorem CurvatureExpression.eval_residual {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : RealTimeInterval.RegularTime D) (k : ℕ) :
    (residual k).eval S (t : ℝ) = rmResidualField S t k := by
  induction k with
  | zero => exact eval_baseResidual S (t : ℝ)
  | succ k ih =>
      simp only [residual, eval, eval_spatialDerivative, eval_comm, eval_gamma,
        rmResidualField, resStarNext, ih]

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]

theorem covariantTimeDerivWithin_curvature_fixed_expression {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (k : ℕ) (t : RealTimeInterval.RegularTime D) (x : M) :
    covariantTimeDerivWithin S.base.metric (fun r => nablaKRm04Field S r k x) D.carrier (t : ℝ) =
      metricTraceFirstTwo0STensor (S.base.metric (t : ℝ))
        (nablaKRm04Field S (t : ℝ) (k + 2) x) + (CurvatureExpression.residual k).eval S (t : ℝ) x +
      ricciTimeCorrection (S.base.metric (t : ℝ)) (nablaKRm04Field S (t : ℝ) k x) := by
  rw [CurvatureExpression.eval_residual]
  exact covariantTimeDerivWithin_curvature_canonical_residual S hS k t x
end DifferentialGeometry.PDE.RicciFlow
