import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ExpressionBounds

set_option autoImplicit false
noncomputable section

open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private def ordinaryRicciTimeExpression : CurvatureExpression 2 :=
  .add CurvatureExpression.ricci.timeDerivative
    (.smul (-1) CurvatureExpression.ricci.ricciAction)

private theorem ordinaryRicciTimeExpression_order :
    ordinaryRicciTimeExpression.maxOrder ≤ 2 := by
  have ht := CurvatureExpression.maxOrder_timeDerivative_le CurvatureExpression.ricci
  have ha : CurvatureExpression.ricci.ricciAction.maxOrder = 0 := rfl
  change max CurvatureExpression.ricci.timeDerivative.maxOrder
    CurvatureExpression.ricci.ricciAction.maxOrder ≤ 2
  rw [ha]
  exact max_le (show CurvatureExpression.ricci.timeDerivative.maxOrder ≤ 2 from ht) (by decide)

def ricciOrdinaryTimeBound (d : ℕ) (C : ℝ) : ℝ :=
  ordinaryRicciTimeExpression.normBound d C

theorem ricciOrdinaryTimeBound_nonneg (d : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ ricciOrdinaryTimeBound d C :=
  ordinaryRicciTimeExpression.normBound_nonneg d C hC

section Generic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

private theorem ordinaryRicciTimeExpression_eval {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (t : RealTimeInterval.RegularTime D) (x : M) :
    derivWithin (fun r => metricRicciAt (S.base.metric r) x) D.carrier (t : ℝ) =
      ordinaryRicciTimeExpression.eval S (t : ℝ) x := by
  have ht := CurvatureExpression.ricci.eval_timeDerivative S hS t x
  have ha := CurvatureExpression.ricci.eval_ricciAction S (t : ℝ) x
  simp only [covariantTimeDerivWithin, CurvatureExpression.eval_ricci] at ht
  simp only [CurvatureExpression.eval_ricci] at ha
  rw [← ha] at ht
  change derivWithin (fun r => metricRicciAt (S.base.metric r) x) D.carrier (t : ℝ) =
    CurvatureExpression.ricci.timeDerivative.eval S (t : ℝ) x +
      (-1 : ℝ) • CurvatureExpression.ricci.ricciAction.eval S (t : ℝ) x
  rw [neg_one_smul]
  simpa only [sub_eq_add_neg] using (eq_sub_iff_add_eq.mpr ht)

theorem metricRicciAt_differentiableWithinAt {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (t : RealTimeInterval.RegularTime D) (x : M) :
    DifferentiableWithinAt ℝ (fun r => metricRicciAt (S.base.metric r) x)
      D.carrier (t : ℝ) := by
  simpa only [CurvatureExpression.eval_ricci] using
    CurvatureExpression.ricci.eval_differentiableWithinAt S hS t x

theorem ricci_ordinary_time_derivative_bound {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (t : RealTimeInterval.RegularTime D) (x : M) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ k ≤ 2,
      Real.sqrt (nablaKRm04NormSqIntrinsic S k (t : ℝ) x) ≤ C) :
    Real.sqrt (normSq0S (S.base.metric (t : ℝ)) x 2
      (derivWithin (fun r => metricRicciAt (S.base.metric r) x) D.carrier (t : ℝ))) ≤
        ricciOrdinaryTimeBound (Module.finrank ℝ E) C := by
  rw [ordinaryRicciTimeExpression_eval S hS t x]
  exact ordinaryRicciTimeExpression.eval_norm_le S (t : ℝ) x C hC
    (fun k hk => hbound k (hk.trans ordinaryRicciTimeExpression_order))

end Generic

end DifferentialGeometry.PDE.RicciFlow
end
