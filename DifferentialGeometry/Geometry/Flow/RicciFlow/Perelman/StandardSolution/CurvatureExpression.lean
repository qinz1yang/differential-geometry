import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.StarSum.Binary
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.PDE.RicciFlow

inductive CurvatureExpression : ℕ → Type where
  | curvature (k : ℕ) : CurvatureExpression (4 + k)
  | zero (s : ℕ) : CurvatureExpression s
  | add {s : ℕ} (A B : CurvatureExpression s) : CurvatureExpression s
  | smul {s : ℕ} (c : ℝ) (A : CurvatureExpression s) : CurvatureExpression s
  | product {s q : ℕ} (A : CurvatureExpression s) (B : CurvatureExpression q) :
      CurvatureExpression (s + q)
  | perm {s s' : ℕ} (e : Fin s ≃ Fin s') (A : CurvatureExpression s) : CurvatureExpression s'
  | trace {s : ℕ} (A : CurvatureExpression (s + 2)) : CurvatureExpression s

def CurvatureExpression.spatialDerivative : {s : ℕ} →
    CurvatureExpression s → CurvatureExpression (s + 1)
  | _, .curvature k => .curvature (k + 1)
  | _, .zero s => .zero (s + 1)
  | _, .add A B => .add A.spatialDerivative B.spatialDerivative
  | _, .smul c A => .smul c A.spatialDerivative
  | _, .product (s := s) (q := q) A B =>
      .add (.perm (leibnizLeftEquiv s q) (.product A.spatialDerivative B))
        (.perm (leibnizRightEquiv s q) (.product A B.spatialDerivative))
  | _, .perm e A => .perm (frontExtendEquiv e) A.spatialDerivative
  | s, .trace A => .trace (.perm (traceNablaShuffle s) A.spatialDerivative)

private def baseTerm (e : Fin 8 ≃ Fin 8) : CurvatureExpression 4 :=
  .trace (.trace (.perm e (.product (.curvature 0) (.curvature 0))))

def CurvatureExpression.baseResidual : CurvatureExpression 4 :=
  .add (.add (.add (.add (.add (.add (.add
    (.smul (-2) (baseTerm btPermE)) (.smul 2 (baseTerm σBt2)))
    (.smul (-2) (baseTerm σBt3))) (.smul 2 (baseTerm σBt4)))
    (baseTerm σD1)) (baseTerm σD2)) (baseTerm σD3)) (baseTerm σD4)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

def CurvatureExpression.eval {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) : {s : ℕ} → CurvatureExpression s →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) s
  | _, .curvature k => nablaKRm04Field S t k
  | _, .zero _ => 0
  | _, .add A B => A.eval S t + B.eval S t
  | _, .smul c A => c • A.eval S t
  | _, .product A B => tensor0SFieldProduct ∞ (A.eval S t) (B.eval S t)
  | _, .perm e A => Tensor0SField.domDomCongr ∞ e (A.eval S t)
  | _, .trace A => metricTraceFirstTwoField (S.family.metric t) (A.eval S t)

variable [CompleteSpace E]

theorem CurvatureExpression.eval_spatialDerivative_realizes {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) {s : ℕ} (A : CurvatureExpression s) :
    TotalNabla0SRealizes (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      s (S.family.connection t) (A.eval S t) (A.spatialDerivative.eval S t) := by
  induction A with
  | curvature k => exact nablaKRm04Field_realizes S t k
  | zero s => exact zero_realizes_nabla s (S.family.connection t)
  | add A B ihA ihB => exact ihA.add ihB
  | smul c A ih => exact ih.smul c
  | product A B ihA ihB =>
      exact nabla0S_product_realizes (S.family.connection t) (A.eval S t) (B.eval S t)
        (A.spatialDerivative.eval S t) (B.spatialDerivative.eval S t) ihA ihB
  | perm e A ih =>
      exact totalNabla0SRealizes_domDomCongr (S.family.connection t) e
        (A.eval S t) (A.spatialDerivative.eval S t) ih
  | trace A ih =>
      have hmc : IsMetricCompatible (S.family.connection t) (S.family.metric t) := by
        simpa only [SolutionOn.family_connection, SolutionFamily.connection, SolutionOn.family_metric] using
          leviCivitaConnectionOfMetric_isMetricCompatible (S.base.metric t)
      exact nablaRealizes_metricTraceFirstTwo (S.family.connection t) (S.family.metric t) hmc
        (A.eval S t) (A.spatialDerivative.eval S t) ih

theorem CurvatureExpression.eval_spatialDerivative {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) {k : ℕ} (A : CurvatureExpression (4 + k)) :
    A.spatialDerivative.eval S t = stNabla S t (A.eval S t) :=
  totalNabla0SRealizes_unique (A.eval_spatialDerivative_realizes S t) (stNabla_realizes S t _)

theorem CurvatureExpression.eval_baseResidual {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) :
    CurvatureExpression.baseResidual.eval S t = e0Field S t := by
  rfl
end DifferentialGeometry.PDE.RicciFlow
