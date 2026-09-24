import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.TimeJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureFields

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle _root_.Manifold Filter Set
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators

section Ancient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance ordinaryMetricC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


theorem closedWindow_metric_time_jet_component_eq_polynomial
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b t : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = Set.Icc a b) (hregular : Set.Ioo a b ⊆ D.regular)
    (ht : t ∈ Set.Icc c b) (x : M) {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (q : ℕ) (slots : Fin 2 → Fin n) :
    component0S (I := I) basis
      (iteratedDerivWithin (q + 1) (fun s => metricTensorField (S.base.metric s) x) (Set.Icc c b) t) slots =
    MvPolynomial.eval
      (curvatureTimePolynomialValues S.base.metric
        (fun r s => mixedCurvatureTensor S 0 r s x) basis t)
      (ordinaryMetricJetPolynomial q slots) := by
  exact ordinary_metric_time_jet_component_eq_polynomial_on_closed_interval
    S hS hac hcb hcarrier hregular ht x basis q slots

end Ancient
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
