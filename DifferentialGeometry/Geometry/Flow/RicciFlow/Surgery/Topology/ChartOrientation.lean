import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChartSimplexBlend


noncomputable section
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

theorem exists_unique_localOrientationClass_from_chart_comparison
    (o : TangentOrientationSection M) (x : M) :
    ∃! xi : LocalIntegralHomology M x 3, ∀ S : OrientedChartSimplex o x, S.localClass = xi := by
  obtain ⟨S⟩ := exists_orientedChartSimplex o x
  exact ⟨S.localClass, fun T => T.localClass_eq_of_positive_charts S,
    fun xi hxi => (hxi S).symm⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
