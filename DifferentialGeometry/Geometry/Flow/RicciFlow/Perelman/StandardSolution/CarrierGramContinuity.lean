import DifferentialGeometry.Geometry.Operator.Family.Gram.Carrier

set_option autoImplicit false

noncomputable section

open Bundle Set DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open scoped BigOperators ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

section GramOperator

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem chartGramOp_continuousOn_carrier
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJ : J ⊆ D.carrier) (x₀ : M) {K : Set E}
    (hK : K ⊆ interior (extChartAt I x₀).target) :
    ContinuousOn (chartGramOp (I := I) G x₀) (J ×ˢ K) := by
  exact DifferentialGeometry.Geometry.Curvature.chartGramOp_continuousOn_of_carrier
    hG hJ x₀ (hK.trans interior_subset)

end GramOperator

end DifferentialGeometry.PDE.RicciFlow

end
